
	
sig Customer{
	opens: set Reservation
}

sig StoreOwner{
	owns: set Store
}

-- how to model that each store has a capacity?
sig Store{
	currentOccupation: one Int,
	maximumOccupation: one Int
}
{
	-- store has at most one owner
	no s: Store, disj o1, o2: StoreOwner | s in o1.owns and s in o2.owns
	--store has at least one owner
	all s: Store | some o: StoreOwner | s in o.owns

	currentOccupation >= 0
	maximumOccupation >= 0
}

sig TimeInterval{}

abstract sig Reservation{
	refersTo: one Store,
	state: one ReservationState,
	timeToReachStore: one Int,
	timeToWait: one Int,
	alertedCustomer: one Bool,
	creationTime: one Int
}
{
	-- reservation is opened by at most one customer
	no r: Reservation, disj c1, c2: Customer | r in c1.opens and r in c2.opens
	-- reservation is opened by at least one customer
	all r: Reservation | some c: Customer | r in c.opens

	creationTime >= 0
	timeToReachStore >= 0
	timeToWait >= 0
}

sig ImmediateReservation extends Reservation {}
sig OnPremiseReservation extends Reservation {}
sig FutureReservation extends Reservation {
-- when booking a future reservation a customer specifies a target time.
-- In most cases target time and entry time coincide; the latter may be 
-- greater than the former in case of delays.
	entryTime: one Int
}

-- Non ubiquity of customer
fact nonUbiquityCurrentCustomer{
	all c: Customer | no disj r1, r2: Reservation | r1 in c.opens and r2 in c.opens and r1.state = CURRENT and r2.state = CURRENT
}

abstract sig ReservationState{}
{
	all rs: ReservationState | some r: Reservation | r.state = rs
}

-- Reservation has been requested but customer cannot yet access the store
sig PENDING extends ReservationState{}
-- Customer can access the store for a time window
sig AUTHORIZED extends ReservationState{}
-- Customer has accessed the store but has not exited yet
sig CURRENT extends ReservationState{}
-- Customer has exited the store or the time window to enter the store ended or the reservation was deleted
sig EXPIRED extends ReservationState{}

abstract sig Bool {}
one sig True, False extends Bool{}

pred isTrue[b: Bool] { b in True }
pred isFalse[b: Bool] { b in False }


fun storeReservations [s: Store] : set Reservation {
	refersTo.s
}
fun storeReservationStates [s: Store] : set ReservationState {
	storeReservations[s].state
}

fact currentStoreOccupationEqualsCurrentReservations {
	all s: Store | let rs = storeReservationStates[s] | s.currentOccupation = #(rs :> CURRENT)
}

fact oneStateForEachReservation {
	no disj r1, r2: Reservation | r1.state = r2.state
}

fact noExceedMaximumOccupation {
	all s: Store | s.maximumOccupation >= s.currentOccupation
}

fact customerAlertedWhenNecessary {
	all r: Reservation | (r in FutureReservation or r in ImmediateReservation)
	and r.timeToWait <= r.timeToReachStore implies isTrue[r.alertedCustomer]
}

fact onPremiseCustomersCantBeAlerted {
	all r: OnPremiseReservation | isFalse[r.alertedCustomer]
}

fact nonPendingReservationHaveNoWaitTime {
	all r: Reservation | (r.state not in PENDING) implies r.timeToWait = 0
}

fact pendingReservationHasPositiveTimeToWait {
	all r: Reservation | r.state in PENDING implies r.timeToWait > 0
}

fact onPremiseReservationsHaveNoTimeToReachStore {
	all r: OnPremiseReservation | r.timeToReachStore = 0
}

fact  noPhysicalQueueOutsideStore {
	all r: Reservation | ((r in ImmediateReservation or r in FutureReservation)
	and r.state not in CURRENT) implies r.timeToReachStore > 0
}

fact  afterEnteringTimeToReachStoreIsNull {
	all r: Reservation | r.state in CURRENT implies r.timeToReachStore = 0
	all r: Reservation | r.state in EXPIRED implies r.timeToReachStore = 0
}

fact noDoubleImmediateReservationForSameCustomer {
	no disj r1, r2: ImmediateReservation | some c: Customer | r1 in c.opens and r2 in c.opens
}

fact noDoubleOnPremiseReservationForSameCustomer {
	no disj r1, r2: OnPremiseReservation | some c: Customer | r1 in c.opens and r2 in c.opens
}


-- Physical reservations (on premise and immediate) follow a FIFO policy:
-- The customer that creates the reservation first, enters first.
fact FIFOQueue {
	all r1, r2: Reservation | ((r1 in OnPremiseReservation or r1 in ImmediateReservation)
	and (r2 in OnPremiseReservation or r2 in ImmediateReservation) and
	(r1.creationTime < r2.creationTime)) implies (r1.timeToWait <= r2.timeToWait)
}

-- When creating a future reservation the target time must be greater that the current time for an amount 
-- represented in this case by 1
fact DelayBetweenCreationAndTargetTime {
	all r: FutureReservation | r.entryTime - r.creationTime > 1
}


fact timeToWaitLessThanDifference {
	all r: FutureReservation | r.timeToWait <= r.entryTime - r.creationTime
}

pred basicModel{
	#Customer >=3
	#CURRENT >=3
	#EXPIRED > 1
	#AUTHORIZED > 1
	#PENDING > 1
	#Store > 1
	#ImmediateReservation > 1
	#OnPremiseReservation > 1
	#FutureReservation > 1
}

run basicModel for 20

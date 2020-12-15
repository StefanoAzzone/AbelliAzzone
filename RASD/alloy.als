

		--------------------------
		--      SIGNATURES      --
		--------------------------
 
sig Customer{
	-- list of the reservations he/she requested
	opens: set Reservation
}

sig StoreOwner{
	-- list of the stores he/she/it owns
	owns: set Store
}

sig Store{
	-- current occupation is the number of people currently in the store
	currentOccupation: one Int,
	-- maximum occupation is the maximum number of people that can fit in a store at any given time
	maximumOccupation: one Int
}
{
	-- store has at most one owner
	no s: Store, disj o1, o2: StoreOwner | s in o1.owns and s in o2.owns
	--store has at least one owner
	all s: Store | some o: StoreOwner | s in o.owns

	-- non negativity constraints
	currentOccupation >= 0
	maximumOccupation >= 0
}

abstract sig Reservation{
	-- store to which the reservation refers
	refersTo: one Store,
	-- state can be: pending, authorized, current, expired
	state: one ReservationState,
	-- estimate of time needed to reach the store from the customer location using selected means of transport
	timeToReachStore: one Int,
	-- estimate of time before the customer will be authorized to enter
	timeToWait: one Int,
	-- True iff the customer has been alerted
	alertedCustomer: one Bool,
	-- time of creation of the reservation
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

-- customer wants to queue up immediately
sig ImmediateReservation extends Reservation {}
-- customer wants to queue up immediately on premise
sig OnPremiseReservation extends Reservation {}
-- customer wants to book a visit to the store for a future date
sig FutureReservation extends Reservation {
	-- when booking a future reservation a customer specifies a target time.
	-- In most cases target time and entry time coincide; the latter may be 
	-- greater than the former in case of delays.
	entryTime: one Int
}

abstract sig ReservationState{}
{
	-- a reservation state has meaning if a reservation is in that state
	all rs: ReservationState | some r: Reservation | r.state = rs
}

-- reservation has been requested but customer cannot yet access the store
sig PENDING extends ReservationState{}
-- customer can access the store for a time window
sig AUTHORIZED extends ReservationState{}
-- customer has accessed the store and has not exited yet
sig CURRENT extends ReservationState{}
-- customer has exited the store or the time window to enter the store ended or the reservation was deleted
sig EXPIRED extends ReservationState{}

-- returns reservations referring to store s
fun storeReservations [s: Store] : set Reservation {
	refersTo.s
}

-- returns states of reservations referring to store s
fun storeReservationStates [s: Store] : set ReservationState {
	storeReservations[s].state
}

abstract sig Bool {}
one sig True, False extends Bool{}

pred isTrue[b: Bool] { b in True }
pred isFalse[b: Bool] { b in False }



		--------------------------
		--        FACTS         --
		--------------------------

-- non ubiquity of customer, customer cannot be inside two different stores at the same time
fact nonUbiquityCurrentCustomer{
	all c: Customer | no disj r1, r2: Reservation | r1 in c.opens and r2 in c.opens and r1.state = CURRENT and r2.state = CURRENT
}

-- the number of current reservation referring to a store s equals to s.currentOccupation
fact currentStoreOccupationEqualsCurrentReservations {
	all s: Store | let rs = storeReservationStates[s] | s.currentOccupation = #(rs :> CURRENT)
}

-- each reservation has its own state
fact oneStateForEachReservation {
	no disj r1, r2: Reservation | r1.state = r2.state
}

-- for every store s, s.currentOccupation never exceeds s.maximumOccupation
fact noExceedMaximumOccupation {
	all s: Store | s.maximumOccupation >= s.currentOccupation
}

--  customer that created reservation r is alerted when r.timeToWait <= r.timeToReachStore
fact customerAlertedWhenNecessary {
	all r: Reservation | (r in FutureReservation or r in ImmediateReservation)
	and r.timeToWait <= r.timeToReachStore implies isTrue[r.alertedCustomer]
}

-- on premise customers cannot be alerted (since they have no smartphone)
fact onPremiseCustomersCantBeAlerted {
	all r: OnPremiseReservation | isFalse[r.alertedCustomer]
}

-- for every Reservation r that is not in PENDING state, r.timeToWait is zero
fact nonPendingReservationHaveNoWaitTime {
	all r: Reservation | (r.state not in PENDING) implies r.timeToWait = 0
}

-- for every Reservation r that is in PENDING state, r.timeToWait is greater than zero
fact pendingReservationHasPositiveTimeToWait {
	all r: Reservation | r.state in PENDING implies r.timeToWait > 0
}

-- for every OnPremiseReservation r, r.timeToReachStore is assumed equal to zero
fact onPremiseReservationsHaveNoTimeToReachStore {
	all r: OnPremiseReservation | r.timeToReachStore = 0
}

-- for all virtual reservations r (ImmediateReservation or FutureReservation), 
-- r.timeToReachStore is greater than zero, which is to say they form no physical queue
-- outside the store
fact  noPhysicalQueueOutsideStore {
	all r: Reservation | ((r in ImmediateReservation or r in FutureReservation)
	and r.state not in CURRENT) implies r.timeToReachStore > 0
}

-- after entering a store time to reach the store is zero
fact  afterEnteringTimeToReachStoreIsZero {
	all r: Reservation | r.state in CURRENT implies r.timeToReachStore = 0
	all r: Reservation | r.state in EXPIRED implies r.timeToReachStore = 0
}

-- no customer can make more than one ImmediateReservation
fact noDoubleImmediateReservationForSameCustomer {
	no disj r1, r2: ImmediateReservation | some c: Customer | r1.state != EXPIRED and r2.state != EXPIRED and r1 in c.opens and r2 in c.opens
}

-- no customer can make more than one OnPremiseReservation
fact noDoubleOnPremiseReservationForSameCustomer {
	no disj r1, r2: OnPremiseReservation | some c: Customer | r1.state != EXPIRED and r2.state != EXPIRED and r1 in c.opens and r2 in c.opens
}

-- Physical reservations (on premise and immediate) follow a FIFO policy:
-- The customer that creates the reservation first, enters first.
fact FIFOQueue {
	all r1, r2: Reservation | ((r1 in OnPremiseReservation or r1 in ImmediateReservation)
	and (r2 in OnPremiseReservation or r2 in ImmediateReservation) and
	(r1.creationTime < r2.creationTime)) implies (r1.timeToWait <= r2.timeToWait)
}

-- Future reservations cannot be created after the entry time
fact noTimeTravel {
	no r: FutureReservation | r.creationTime > r.entryTime
}

-- When creating a future reservation the target time must be greater that the current time for an amount 
-- represented in this case by the constant 1
fact DelayBetweenCreationAndTargetTime {
	all r: FutureReservation | r.entryTime - r.creationTime > 1
}

-- for every FutureReservation r, r.timeToWait is dominated by the difference between r.entryTime and r.creationTime
fact timeToWaitLessThanDifference {
	all r: FutureReservation | r.timeToWait <= r.entryTime - r.creationTime
}

-- two future reservation for the same store opened by the same customer cannot have the same target time;
-- between the two there must be a delay represented in this case by the constant 1
fact DelayBetweenTwoFutureReservationForSameStore {
	all r1, r2: FutureReservation | some c : Customer | (r1.refersTo = r2.refersTo and r1 in c.opens and r2 in c.opens) implies (r1.entryTime >= 1 + r2.entryTime
	or r2.entryTime >= 1 + r1.entryTime)
}



		--------------------------
		--      PREDICATES      --
		--------------------------

pred World1(s: Store) {
	s.currentOccupation = 5

	#Customer >= 3
	#EXPIRED > 0
	#AUTHORIZED > 0
	#PENDING > 0
	#Store = 1
	#ImmediateReservation >= 0
	#OnPremiseReservation = 1
	#FutureReservation = 1
}

run World1 for 20

pred World2(r1, r2 : ImmediateReservation) {
	r1.alertedCustomer = False
	r2.alertedCustomer = True

	r1.creationTime > r2.creationTime
	r1.timeToWait > r2.timeToWait

	r1.refersTo = r2.refersTo

	#Reservation > 3
	#Customer >=3
	#Store >= 3
	#StoreOwner >= 2
}

run World2 for 20

pred World3() {

	#Customer >= 3
	#CURRENT > 0
	#EXPIRED > 0
	#AUTHORIZED > 0
	#PENDING > 0
	#ImmediateReservation >= 0
	#OnPremiseReservation = 1
	#FutureReservation > 2
}

run World3 for 20
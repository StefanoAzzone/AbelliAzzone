	
sig Customer{
	opens: set Reservation
}

sig StoreOwner{
	owns: set Store
}

-- how to model that each store has a capacity?
sig Store{
	
}
{
	-- store has at most one owner
	no s: Store, disj o1, o2: StoreOwner | s in o1.owns and s in o2.owns
	--store has at least one owner
	all s: Store | some o: StoreOwner | s in o.owns
}

abstract sig Reservation{
	refersTo: one Store
}
{
	-- reservation is opened by at most one customer
	no r: Reservation, disj c1, c2: Customer | r in c1.opens and r in c2.opens
	-- reservation is opened by at least one customer
	all r: Reservation | some c: Customer | r in c.opens
}

-- Reservation has been requested but customer cannot yet access the store
sig PendingReservation extends Reservation{}
-- Customer can access the store for a time window
sig AuthorizedReservation extends Reservation{}
-- Customer has accessed the store but has not exited yet
sig CurrentReservation extends Reservation{}
{
	-- Non ubiquity of customer
	all c: Customer | no disj r1, r2: CurrentReservation | r1 in c.opens and r2 in c.opens
}
-- Customer has exited the store or the time window to enter the store ended
sig ExpiredReservation extends Reservation{}

pred show{
	#Customer >=3
}

run show for 5


sig Customer{
	opens: set Reservation
}

sig StoreOwner{
	owns: set Store
}

sig Store{}
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

sig ImmediateReservation extends Reservation{}
sig FutureReservation extends Reservation{}
sig OnPremiseReservation extends Reservation{}

pred show{
	#Customer >=3
}

run show for 5

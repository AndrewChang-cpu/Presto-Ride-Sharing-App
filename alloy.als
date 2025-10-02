sig Presto {
	riders: set Rider,
	available_driver : set Available,
	offline_driver : set Offline,
	driving_driver : set Driving,
	pending_request: set PendingReq,
	riding_request: set RidingReq,
	// at most one active request per rider
	requests: Rider -> lone Request,
	// each driving driver is assigned to exactly one ride request
	assigned: Driving -> one RidingReq
}

sig Rider {
	// at most one active request
}

abstract sig Driver {
	// rider may be assigned a driver
	operatesIn: some Region
}
sig Available, Offline extends Driver {}
sig Driving extends Driver {
	// must be assigned to exactly one ride request
}

sig Region {
	// each region covers some locations
	contains: some Location
}
sig Location {}

// Ride requests
abstract sig Request {
	origin: one Location,
	dest: one Location,
}
sig PendingReq extends Request {}
sig RidingReq extends Request {}


pred invariants[p: Presto] {
	// Each Ride request must have different origin and destination
	all req : p.pending_request + p.riding_request | req.origin != req.dest

	// Every location must belong to exactly one region


	// --- State consistency for requests ---
	// The set of requests in the `requests` relation must be the union of pending and riding requests
	p.riders.(p.requests) = p.pending_request + p.riding_request
	// Every ride request must be owned by exactly one rider
	all rq : p.pending_request + p.riding_request | one r : p.riders | r.(p.requests) = rq

	// --- State consistency for assigned drivers ---
	// The domain of the `assigned` relation must be the set of all driving drivers
	p.assigned.RidingReq = p.driving_driver
	// Each Riding request must be assigned to exactly one Driving driver
	all rq : p.riding_request | one d : p.driving_driver | d.(p.assigned) = rq
}


fact {
	all r: Rider | some p : Presto | r in p.rider
	all d: Driver | some p : Presto | d in p.available_driver + p.offline_driver + p.driving_driver
	all req: Request | some p : Presto | req in p.pending_request + p.riding_request

	all l: Location | one r: Region | l in r.contains
}


pred op_request[p1, p2 : Presto, r : Rider, req : PendingReq] {
	// precondition: request locations must be different
	req.origin != req.dest

	// precondition: no rider should already be assigned to request
	no other : Rider | other != r and p1.requests[other] = req

	// precondition: rider has no active request
	no r.(p1.requests)

	// post: rider now holds the request
	p2.requests = p1.requests + (r -> req)

	// post: add req to pending_request set
	p2.pending_request = p1.pending_request + req

	// everything else unchanged
	p2.rider = p1.rider
	p2.available_driver = p1.available_driver
	p2.offline_driver = p1.offline_driver
	p2.driving_driver = p1.driving_driver
	p2.riding_request = p1.riding_request
	p2.region = p1.region
	p2.location = p1.location
	p2.assigned = p1.assigned
}

pred op_cancel[p1, p2 : Presto, r : Rider] {
	// precondition: rider has a pending request
	one r.(p1.requests) and r.(p1.requests) in p1.pending_request

	// post: rider has no active request
	p2.requests = p1.requests - (r -> r.(p1.requests))

	// post: remove request from pending_request set
	p2.pending_request = p1.pending_request - r.(p1.requests)

	// everything else unchanged
	p2.rider            = p1.rider
	p2.available_driver = p1.available_driver
	p2.offline_driver   = p1.offline_driver
	p2.driving_driver   = p1.driving_driver
	p2.riding_request   = p1.riding_request
	p2.region           = p1.region
	p2.location         = p1.location
	p2.assigned         = p1.assigned
}


pred op_match[p1, p2 : Presto, r : Rider, d : Driver, ride : RidingReq] {
	// precondition: rider has a pending request
	let req = r.(p1.requests) {
		some req and req in p1.pending_request
	}
	// precondition: driver is available
	d in p1.available_driver
	// precondition: request locations not in driver regions implies that no other available drivers have regions that match the request locations
	let req = r.(p1.requests) {
	   (req.origin !in d.operatesIn.contains or req.dest !in d.operatesIn.contains) implies
			no other : p1.available_driver - d | (req.origin in other.operatesIn.contains and req.dest in other.operatesIn.contains)
	}

	// post: rider’s pending request becomes a riding request
	p2.requests = p1.requests - (r -> r.(p1.requests)) + (r -> ride)

	// post: driver moves from available to driving and is assigned
	p2.assigned = p1.assigned + (d -> ride)

	// update system sets
	p2.pending_request  = p1.pending_request - r.(p1.requests)
	p2.riding_request   = p1.riding_request + ride
	p2.available_driver = p1.available_driver - d
	p2.driving_driver   = p1.driving_driver + d

	// everything else unchanged
	p2.rider            = p1.rider
	p2.offline_driver   = p1.offline_driver
	p2.region           = p1.region
	p2.location         = p1.location
}


pred op_complete[p1, p2 : Presto, r : Rider, d : Driver] {
	// precondition: rider is in RidingReq assigned to d
	d in p1.driving_driver
	r.(p1.requests) = d.(p1.assigned)
	r.(p1.requests) in p1.riding_request

	// post: rider has no active request
	p2.requests = p1.requests - (r -> r.(p1.requests))
	
	// post: driver is no longer assigned a request
	p2.assigned = p1.assigned - (d -> d.(p1.assigned))

	// update system sets
	p2.riding_request   = p1.riding_request - d.(p1.assigned)
	p2.driving_driver   = p1.driving_driver - d
	p2.available_driver = p1.available_driver + d

	// everything else unchanged
	p2.rider            = p1.rider
	p2.offline_driver   = p1.offline_driver
	p2.pending_request  = p1.pending_request
}


assert RequestPreservesInvariants {
  all p1, p2: Presto, r: Rider, req: PendingReq |
	invariants[p1] and op_request[p1, p2, r, req] implies invariants[p2]
}

assert CancelPreservesInvariants {
  all p1, p2: Presto, r: Rider |
	invariants[p1] and op_cancel[p1, p2, r] implies invariants[p2]
}

assert MatchPreservesInvariants {
  all p1, p2: Presto, r: Rider, d: Available, ride: RidingReq |
	invariants[p1] and op_match[p1, p2, r, d, ride] implies invariants[p2]
}

assert CompletePreservesInvariants {
  all p1, p2: Presto, r: Rider, d: Driving |
	invariants[p1] and op_complete[p1, p2, r, d] implies invariants[p2]
}

check RequestPreservesInvariants for 3 but exactly 2 Presto
//check CancelPreservesInvariants for 4
//check MatchPreservesInvariants for 4
//check CompletePreservesInvariants for 4

run GenerateValidInstance {} for 3

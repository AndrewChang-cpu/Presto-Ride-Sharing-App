sig Presto {
	riders: set Rider,
	available_drivers: set Available,
	offline_drivers: set Offline,
	driving_drivers: set Driving,
	pending_requests: set PendingReq,
	riding_requests: set RidingReq,

	// at most one active request per rider
	active_requests: Rider -> lone Request,
	// each driving driver is assigned to exactly one ride request
	driver_assignments: Driving -> one RidingReq
}

sig Rider {}

abstract sig Driver {
	operatesIn: some Region
}
sig Available extends Driver {}
sig Offline extends Driver {}
sig Driving extends Driver {}

sig Region {
	contains: some Location
}
sig Location {}

abstract sig Request {
	origin: one Location,
	dest: one Location,
}
sig PendingReq extends Request {}
sig RidingReq extends Request {}


pred invariants[p: Presto] {
	// Each Ride request must have different origin and destination
	all req : p.pending_requests + p.riding_requests | req.origin != req.dest

	// Every location must belong to exactly one region


	// --- State consistency for requests ---
	// The set of requests in the `requests` relation must be the union of pending and riding requests
	p.riders.(p.active_requests) = p.pending_requests + p.riding_requests
	// Every ride request must be owned by exactly one rider
	all rq : p.pending_requests + p.riding_requests | one r : p.riders | r.(p.active_requests) = rq

	// --- State consistency for assigned drivers ---
	// The domain of the `assigned` relation must be the set of all driving drivers
	p.driver_assignments.RidingReq = p.driving_drivers
	// Each Riding request must be assigned to exactly one Driving driver
	all rq : p.riding_requests | one d : p.driving_drivers | d.(p.driver_assignments) = rq
}


fact {
	all r: Rider | some p : Presto | r in p.riders
	all d: Driver | some p : Presto | d in p.available_drivers + p.offline_drivers + p.driving_drivers
	all req: Request | some p : Presto | req in p.pending_requests + p.riding_requests

	all l: Location | one r: Region | l in r.contains
}


pred op_request[p1, p2 : Presto, r : Rider, req : PendingReq] {
	// precondition: request locations must be different
	req.origin != req.dest

	// precondition: no rider should already be assigned to request
	no other : Rider | other != r and p1.active_requests[other] = req

	// precondition: rider has no active request
	no r.(p1.active_requests)

	// post: rider now holds the request
	p2.active_requests = p1.active_requests + (r -> req)

	// post: add req to pending_request set
	p2.pending_requests = p1.pending_requests + req

	// everything else unchanged
	p2.riders = p1.riders
	p2.available_drivers = p1.available_drivers
	p2.offline_drivers = p1.offline_drivers
	p2.driving_drivers = p1.driving_drivers
	p2.riding_requests = p1.riding_requests
	p2.driver_assignments = p1.driver_assignments
}

pred op_cancel[p1, p2 : Presto, r : Rider] {
	// precondition: rider has a pending request
	one r.(p1.active_requests) and r.(p1.active_requests) in p1.pending_requests

	// post: rider has no active request
	p2.active_requests = p1.active_requests - (r -> r.(p1.active_requests))

	// post: remove request from pending_request set
	p2.pending_requests = p1.pending_requests - r.(p1.active_requests)

	// everything else unchanged
	p2.riders = p1.riders
	p2.available_drivers = p1.available_drivers
	p2.offline_drivers = p1.offline_drivers
	p2.driving_drivers = p1.driving_drivers
	p2.riding_requests = p1.riding_requests
	p2.driver_assignments = p1.driver_assignments
}


pred op_match[p1, p2 : Presto, r : Rider, d : Driver, ride : RidingReq] {
	// precondition: rider has a pending request
	let req = r.(p1.active_requests) {
		some req and req in p1.pending_requests
	}
	// precondition: driver is available
	d in p1.available_drivers
	// precondition: request locations not in driver regions implies that no other available drivers have regions that match the request locations
	let req = r.(p1.active_requests) {
	   (req.origin !in d.operatesIn.contains or req.dest !in d.operatesIn.contains) implies
			no other : p1.available_drivers - d | (req.origin in other.operatesIn.contains and req.dest in other.operatesIn.contains)
	}

	// post: rider’s pending request becomes a riding request
	p2.active_requests = p1.active_requests - (r -> r.(p1.active_requests)) + (r -> ride)

	// post: driver moves from available to driving and is assigned
	p2.driver_assignments = p1.driver_assignments + (d -> ride)

	// update system sets
	p2.pending_requests = p1.pending_requests - r.(p1.active_requests)
	p2.riding_requests = p1.riding_requests + ride
	p2.available_drivers = p1.available_drivers - d
	p2.driving_drivers = p1.driving_drivers + d

	// everything else unchanged
	p2.riders = p1.riders
	p2.offline_drivers = p1.offline_drivers
}


pred op_complete[p1, p2 : Presto, r : Rider, d : Driver] {
	// precondition: rider is in RidingReq assigned to d
	d in p1.driving_drivers
	r.(p1.active_requests) = d.(p1.driver_assignments)
	r.(p1.active_requests) in p1.riding_requests

	// post: rider has no active request
	p2.active_requests = p1.active_requests - (r -> r.(p1.active_requests))
	
	// post: driver is no longer assigned a request
	p2.driver_assignments = p1.driver_assignments - (d -> d.(p1.driver_assignments))

	// update system sets
	p2.riding_requests = p1.riding_requests - d.(p1.driver_assignments)
	p2.driving_drivers = p1.driving_drivers - d
	p2.available_drivers = p1.available_drivers + d

	// everything else unchanged
	p2.riders = p1.riders
	p2.offline_drivers = p1.offline_drivers
	p2.pending_requests = p1.pending_requests
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

//check RequestPreservesInvariants for 3 but exactly 2 Presto
//check CancelPreservesInvariants for 4
//check MatchPreservesInvariants for 4
//check CompletePreservesInvariants for 4

run GenerateValidInstance {} for 3 but exactly 1 Region, exactly 2 Location, exactly 1 Driver, exactly 1 Presto

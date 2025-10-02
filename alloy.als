sig Presto {
	available_driver : set Driver,
	offline_driver : set Driver,
	driving_driver : set Driver,
	pending_request: set Request,
	riding_request: set Request,
	// at most one active request per rider
	requests: Rider lone -> lone Request,
	// each driving driver is assigned to exactly one ride request
	assigned: Driver lone -> lone Request
}

sig Rider {
	// at most one active request
}

sig Driver {
	// rider may be assigned a driver
	operatesIn: some Region
}

sig Region {
	// each region covers some locations
	contains: some Location
}
sig Location {}

// Ride requests
sig Request {
	origin: one Location,
	dest: one Location,
}


pred invariants[p: Presto] {
    // --- Disjointness Constraints ---
    // A driver cannot be in more than one state at a time
    no p.available_driver & p.driving_driver
    no p.available_driver & p.offline_driver
    no p.driving_driver & p.offline_driver

    // A request cannot be both pending and riding
    no p.pending_request & p.riding_request

    // --- Core Logic ---
    // Each Ride request must have different origin and destination
    all req : p.pending_request + p.riding_request | req.origin != req.dest

    // --- State Consistency for requests ---
    // Pending requests and riding requests make up all requests
    Rider.(p.requests) = p.pending_request + p.riding_request

    // --- State Consistency for assigned drivers ---
    // The domain of the `assigned` relation must be the set of all driving drivers
    p.assigned.Request = p.driving_driver

    // The range of the `assigned` relation must be the set of all riding requests
    p.driving_driver.(p.assigned) = p.riding_request
}


fact {
    all d : Driver | some p : Presto | d in p.available_driver + p.offline_driver + p.driving_driver
    all req : Request | some p : Presto | req in p.pending_request + p.riding_request

    // Every location must belong to exactly one region
    all l : Location | one r : Region | l in r.contains
}


pred op_request[p1, p2 : Presto, r : Rider, req : Request] {
	// precondition: request locations must be different
	req.origin != req.dest

	// precondition: no rider should already be assigned to request
	//no other : Rider | other != r and p1.requests[other] = req
	req !in (p1.pending_request + p1.riding_request)

	// precondition: rider has no active request
	no r.(p1.requests)

	// post: rider now holds the request
	p2.requests = p1.requests + (r -> req)

	// post: add req to pending_request set
	p2.pending_request = p1.pending_request + req

	// everything else unchanged
	p2.available_driver = p1.available_driver
	p2.offline_driver = p1.offline_driver
	p2.driving_driver = p1.driving_driver
	p2.riding_request = p1.riding_request
	p2.assigned = p1.assigned
}

pred op_cancel[p1, p2 : Presto, r : Rider] {
    // precondition: rider has a request
    one p1.requests[r]

    // precondition: request is pending
    p1.requests[r] in p1.pending_request

    // post: rider has no active request
    p2.requests = p1.requests - (r -> p1.requests[r])

    // post: remove request from pending_request set
    p2.pending_request = p1.pending_request - p1.requests[r]

    // everything else unchanged
    p2.available_driver = p1.available_driver
    p2.offline_driver   = p1.offline_driver
    p2.driving_driver   = p1.driving_driver
    p2.riding_request   = p1.riding_request
    p2.assigned         = p1.assigned
}

// Helper predicate to check if a request is within a driver's regions
pred is_in_regions[d: Driver, req: Request] {
    req.origin in d.operatesIn.contains and req.dest in d.operatesIn.contains
}
pred op_match[p1, p2 : Presto, r : Rider, d : Driver] {
    let req = r.(p1.requests) {
        // precondition: rider has a pending request
        some req and req in p1.pending_request

	// precondition: driver is available
        d in p1.available_driver

        // precondition: a driver can be matched if they are in the request's region,
        // or if no other available driver is in the request's region.
        is_in_regions[d, req] or (no other : p1.available_driver | is_in_regions[other, req])

        // post:
        p2.assigned = p1.assigned + (d -> req)
        p2.pending_request  = p1.pending_request - req
        p2.riding_request   = p1.riding_request + req
        p2.available_driver = p1.available_driver - d
        p2.driving_driver   = p1.driving_driver + d

        // Specify which relations remain unchanged
        p2.requests         = p1.requests
        p2.offline_driver   = p1.offline_driver
    }
}

pred op_complete[p1, p2 : Presto, r : Rider, d : Driver] {
    // precondition: rider is in RidingReq assigned to d
    d in p1.driving_driver
    r.(p1.requests) = d.(p1.assigned)

    // post: rider has no active request
    p2.requests = p1.requests - (r -> r.(p1.requests))
    
    // post: driver is no longer assigned a request
    p2.assigned = p1.assigned - (d -> d.(p1.assigned))

    // update system sets
    p2.riding_request   = p1.riding_request - d.(p1.assigned)
    p2.driving_driver   = p1.driving_driver - d
    p2.available_driver = p1.available_driver + d

    // everything else unchanged
    p2.offline_driver   = p1.offline_driver
    p2.pending_request  = p1.pending_request
}


assert RequestPreservesInvariants {
  all p, p2 : Presto, r : Rider, req : Request |
    invariants[p] and op_request[p, p2, r, req] implies invariants[p2]
}

assert CancelPreservesInvariants {
  all p, p2 : Presto, r : Rider |
    invariants[p] and op_cancel[p, p2, r] implies invariants[p2]
}

assert MatchPreservesInvariants {
  all p, p2 : Presto, r : Rider, d : Driver |
    invariants[p] and op_match[p, p2, r, d] implies invariants[p2]
}

assert CompletePreservesInvariants {
  all p, p2 : Presto, r : Rider, d : Driver |
    invariants[p] and op_complete[p, p2, r, d] implies invariants[p2]
}

check RequestPreservesInvariants for 7
check CancelPreservesInvariants for 7
check MatchPreservesInvariants for 7
check CompletePreservesInvariants for 7

run GenerateValidInstance {
  //some p, p2 : Presto, r : Rider, req : PendingReq | op_request[p, p2, r, req]
  //some p, p2 : Presto, r : Rider | op_cancel[p, p2, r]
  //some p, p2 : Presto, r : Rider, a : Available, rq : RidingReq | op_match[p, p2, r, a, rq]
  some p, p2 : Presto, r : Rider, d : Driver | op_complete[p, p2, r, d]
	
  #Presto=2
  //#Region=2
  //#Location=1
  //#Available=1
  //#Driving=2
  //#PendingReq >= 1
  //#RidingReq >= 1
  //#Request>1
} for 2

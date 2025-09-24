sig Presto {
	rider: set Rider,
	available_driver : set Available,
	offline_driver : set Offline,
	pending_request: set PendingReq,
	riding_request: set RidingReq,
	region: set Region,
	location: set Location
}

sig Rider {
	// at most one active request
	requests: lone Request
}

abstract sig Driver {
	// rider may be assigned a driver
	operatesIn: set Region
}
sig Available, Offline extends Driver {}
sig Driving extends Driver {
	// must be assigned to exactly one ride request
	assigned: one RidingReq
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

pred UNUSEDinvariants[p: Presto] {
	// TODO make invariants take on argument p

	// Each Ride request must have different origin and destination
	all req : Request | req.origin != req.dest

	// Each Riding request must be assigned to exactly one Driving driver
	all rq: RidingReq | one d: Driving | rq in d.assigned
	all l : Location | one r : Region | l in r.contains
    
	// Every ride request must have one rider
	all rq : Request | one r: Rider | r.requests = rq

	// Make sure pending req and available driver with no regions never exist
}

pred invariants[p: Presto] {
    // Each Ride request must have different origin and destination
    all req : p.pending_request + p.riding_request | req.origin != req.dest

    // Each Riding request must be assigned to exactly one Driving driver
    all rq : p.riding_request | one d : Driving | rq in d.assigned

    // Every location must belong to exactly one region
    all l : p.location | one r : p.region | l in r.contains

    // Every ride request must have one rider in p.rider
    all rq : p.pending_request + p.riding_request | one r : p.rider | r.requests = rq

    // Example placeholder: forbid available drivers with no regions
    all d : p.available_driver | some d.operatesIn
}


pred op_request[p, p' : Presto, r : Rider, req : PendingReq] {
    // precondition: rider has no active request
    no r.requests

    // post: rider now holds the request
    r.requests = req

    // post: add req to pending_request set
    p'.pending_request = p.pending_request + req

    // everything else unchanged
    p'.rider            = p.rider
    p'.available_driver = p.available_driver
    p'.offline_driver   = p.offline_driver
    p'.riding_request   = p.riding_request
    p'.region           = p.region
    p'.location         = p.location
}


pred op_cancel[p, p' : Presto, r : Rider] {
    // precondition: rider has a pending request
    some r.requests and r.requests in p.pending_request

    // post: rider has no active request
    no r.requests

    // post: remove request from pending_request set
    p'.pending_request = p.pending_request - r.requests

    // everything else unchanged
    p'.rider            = p.rider
    p'.available_driver = p.available_driver
    p'.offline_driver   = p.offline_driver
    p'.riding_request   = p.riding_request
    p'.region           = p.region
    p'.location         = p.location
}


pred op_match[p, p' : Presto, r : Rider, d : Available, ride : RidingReq] {
    // precondition: rider has a pending request
    some r.requests and r.requests in p.pending_request

    // post: rider’s pending request becomes a riding request
    r.requests = ride

    // update system sets
    p'.pending_request = p.pending_request - r.requests
    p'.riding_request  = p.riding_request + ride

    // post: driver moves from available to driving and is assigned
    p'.available_driver = p.available_driver - d
    some drv : Driving | drv.assigned = ride

    // everything else unchanged
    p'.rider          = p.rider
    p'.offline_driver = p.offline_driver
    p'.region         = p.region
    p'.location       = p.location
}


pred op_complete[p, p' : Presto, r : Rider, d : Driving] {
    // precondition: rider is in RidingReq assigned to d
    some r.requests and r.requests = d.assigned
    r.requests in p.riding_request

    // post: rider has no active request
    no r.requests

    // update system sets
    p'.riding_request  = p.riding_request - d.assigned
    p'.available_driver = p.available_driver + d

    // everything else unchanged
    p'.rider            = p.rider
    p'.offline_driver   = p.offline_driver
    p'.pending_request  = p.pending_request
    p'.region           = p.region
    p'.location         = p.location
}


assert RequestPreservesInvariants {
  all p, p' : Presto, r : Rider, req : PendingReq |
    invariants[p] and op_request[p, p', r, req] implies invariants[p']
}

assert CancelPreservesInvariants {
  all p, p' : Presto, r : Rider |
    invariants[p] and op_cancel[p, p', r] implies invariants[p']
}

assert MatchPreservesInvariants {
  all p, p' : Presto, r : Rider, d : Available, ride : RidingReq |
    invariants[p] and op_match[p, p', r, d, ride] implies invariants[p']
}

assert CompletePreservesInvariants {
  all p, p' : Presto, r : Rider, d : Driving |
    invariants[p] and op_complete[p, p', r, d] implies invariants[p']
}

check RequestPreservesInvariants for 4 but 2 Presto
check CancelPreservesInvariants for 4 but 2 Presto
check MatchPreservesInvariants for 4 but 2 Presto
check CompletePreservesInvariants for 4 but 2 Presto

run GenerateValidInstance {
    some p : Presto | invariants[p]
 	#Presto=2

  all p, p' : Presto, r : Rider, req : PendingReq |
    invariants[p] and op_request[p, p', r, req] implies invariants[p']
	
    //#Region=2
    //#Location=1
    #PendingReq >= 1
    #RidingReq >= 1
} for 3


//run GenerateValidInstance {
	//invariants
	//#Region=2
	//#Location=1
	//#PendingReq>=2
   	//#RidingReq>=2
//} for 4

sig Presto {
	rider: set Rider,
	available_driver : set Available,
	offline_driver : set Offline,
	driving_driver : set Driving,
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
	operatesIn: some Region
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


pred invariants[p: Presto] {
    // Each Ride request must have different origin and destination
    all req : p.pending_request + p.riding_request | req.origin != req.dest

    // Each Riding request must be assigned to exactly one Driving driver
    all rq : p.riding_request | one d : p.driving_driver | d.assigned = rq

    // Every location must belong to exactly one region
    all l : p.location | one r : p.region | l in r.contains

    // Every ride request must have one rider in p.rider
    all rq : p.pending_request + p.riding_request | one r : p.rider | r.requests = rq
    

}


pred op_request[p1, p2 : Presto, r : Rider, req : PendingReq] {
    // precondition: rider has no active request
    no r.requests

    // post: rider now holds the request
    r.requests = req

    // post: add req to pending_request set
    p2.pending_request = p1.pending_request + req

    // everything else unchanged
    p2.rider            = p1.rider
    p2.available_driver = p1.available_driver
    p2.offline_driver   = p1.offline_driver
    p2.driving_driver   = p1.driving_driver
    p2.riding_request   = p1.riding_request
    p2.region           = p1.region
    p2.location         = p1.location
}


pred op_cancel[p1, p2 : Presto, r : Rider] {
    // precondition: rider has a pending request
    one r.requests and r.requests in p1.pending_request

    // post: rider has no active request
    no r.requests

    // post: remove request from pending_request set
    p2.pending_request = p1.pending_request - r.requests

    // everything else unchanged
    p2.rider            = p1.rider
    p2.available_driver = p1.available_driver
    p2.offline_driver   = p1.offline_driver
    p2.driving_driver   = p1.driving_driver
    p2.riding_request   = p1.riding_request
    p2.region           = p1.region
    p2.location         = p1.location
}


pred op_match[p1, p2 : Presto, r : Rider, d : Available, ride : RidingReq] {
    // precondition: rider has a pending request
    some r.requests and r.requests in p1.pending_request
    // precondition: driver is available
    d in p1.available_driver
    // precondition: request locations not in driver regions implies that no other available drivers have regions that match the request locations
    (r.requests.origin !in d.operatesIn.contains or r.requests.dest !in d.operatesIn.contains) implies
        no other : Available | other != d and (r.requests.origin in other.operatesIn.contains and r.requests.dest in other.operatesIn.contains)

    // post: rider’s pending request becomes a riding request
    r.requests = ride

    // update system sets
    p2.pending_request = p1.pending_request - r.requests
    p2.riding_request  = p1.riding_request + ride

    // post: driver moves from available to driving and is assigned
    p2.available_driver = p1.available_driver - d
    p2.driving_driver   = p1.driving_driver + d
    some drv : Driving | drv.assigned = ride

    // everything else unchanged
    p2.rider          = p1.rider
    p2.offline_driver = p1.offline_driver
    p2.region         = p1.region
    p2.location       = p1.location
}


pred op_complete[p1, p2 : Presto, r : Rider, d : Driving] {
    // precondition: rider is in RidingReq assigned to d
    some r.requests and r.requests = d.assigned
    r.requests in p1.riding_request

    // post: rider has no active request
    no r.requests

    // update system sets
    p2.riding_request  = p1.riding_request - d.assigned
    p2.driving_driver  = p1.driving_driver - d
    p2.available_driver = p1.available_driver + d

    // everything else unchanged
    p2.rider            = p1.rider
    p2.offline_driver   = p1.offline_driver
    p2.pending_request  = p1.pending_request
    p2.region           = p1.region
    p2.location         = p1.location
}


assert RequestPreservesInvariants {
  all p, p2 : Presto, r : Rider, req : PendingReq |
    invariants[p] and op_request[p, p2, r, req] implies invariants[p2]
}

assert CancelPreservesInvariants {
  all p, p2 : Presto, r : Rider |
    invariants[p] and op_cancel[p, p2, r] implies invariants[p2]
}

assert MatchPreservesInvariants {
  all p, p2 : Presto, r : Rider, d : Available, ride : RidingReq |
    invariants[p] and op_match[p, p2, r, d, ride] implies invariants[p2]
}

assert CompletePreservesInvariants {
  all p, p2 : Presto, r : Rider, d : Driving |
    invariants[p] and op_complete[p, p2, r, d] implies invariants[p2]
}

check RequestPreservesInvariants for 4 but 2 Presto
check CancelPreservesInvariants for 4 but 2 Presto
check MatchPreservesInvariants for 4 but 2 Presto
check CompletePreservesInvariants for 4 but 2 Presto

run GenerateValidInstance {
  all p : Presto | invariants[p]
 	#Presto=1

  // all p, p2 : Presto, r : Rider, req : PendingReq |
  //   invariants[p] and op_request[p, p2, r, req] implies invariants[p2]
	
  //#Region=2
  //#Location=1
  #Available=1
  #Driving=2
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

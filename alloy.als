sig Rider {
	// at most one active request
    requests: lone RideReq
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
abstract sig RideReq {
    origin: one Location,
    dest: one Location,
}
sig PendingReq extends RideReq {}
sig RidingReq extends RideReq {}

pred invariants {
    // Each Ride request must have different origin and destination
    all req : RideReq | req.origin != req.dest

    // Each Riding request must be assigned to exactly one Driving driver
    all rq: RidingReq | one d: Driving | rq in d.assigned
    all l: Location | some r: Region | l in r.contains
    
    // Every ride request must have one rider
    all rr : RidingReq | one r: Rider | r.requests = rr
}

run GenerateValidInstance {
    invariants
} for 2

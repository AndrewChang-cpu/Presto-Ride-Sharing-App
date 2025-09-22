// Core entities
sig Rider {
    requests : lone RideReq,       // at most one active request
}

abstract sig Driver {
    operatesIn : set Region       // rider may be assigned a driver
}
sig Available, Offline extends Driver {}
sig Driving extends Driver {
    assigned : one Riding        // must be assigned to exactly one ride request
}

sig Region {
    contains : some Location       // each region covers some locations
}

sig Location {}

// Ride requests
abstract sig RideReq {
    origin : one Location,
    dest   : one Location
}

sig Pending extends RideReq {}
sig Riding extends RideReq {}


pred invariants {
    // 1. Each Rider has at most one active request (already enforced by "lone requests").
    // But if they have one, it must be either Pending or Riding.
    // all r : Rider | lone r.requests implies (r.requests in Pending + Riding)

    // 2. A Driving driver must be assigned to exactly one Riding request
    // all d : Driving | one d.assigned
    // all d : Driving | d.assigned in Riding

    // 3. No Available or Offline driver may be assigned to a request
    // all d : Available + Offline | no r : Riding | d in Driver<:assigned

    // 4. Each request’s origin and destination must belong to exactly one region
    // all req : RideReq | one r1 : Region | req.origin in r1.contains
    // all req : RideReq | one r2 : Region | req.dest   in r2.contains

    // 5. If a driver is assigned to a Riding request, both origin and dest must be in their regions
    // all d : Driving | let ride = d.assigned |
    //     (some reg1 : d.operatesIn | ride.origin in reg1.contains) and
    //     (some reg2 : d.operatesIn | ride.dest   in reg2.contains)

    // 6. Riders with a Riding request are served by exactly one Driving driver
    // all r : Rider | r.requests in Riding implies
    //     one d : Driving | d.assigned = r.requests
}


run GenerateValidInstance {
    invariants
} for 2

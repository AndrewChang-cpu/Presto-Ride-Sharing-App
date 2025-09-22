
sig Rider {
    requests : lone RideReq,      // at most one active request
}
abstract sig Driver {
    operatesIn : set Region       // rider may be assigned a driver
}
sig Available, Offline extends Driver {}
sig DrivingDriver extends Driver {
    assigned : one RidingReq        // must be assigned to exactly one ride request
}
sig Region {
    contains : some Location       // each region covers some locations
}
sig Location {}
// Ride requests
abstract sig RideReq {
    origin : one Location,
    dest   : one Location,
    rider  : one Rider
}
sig PendingReq extends RideReq {}
sig RidingReq extends RideReq {
    // TODO thinkn about why we need to get rid of this
    // driver : one DrivingDriver          // must be assigned to exactly one driver
}
pred invariants {
    // 1. Each Ride request must have different origin and destination
    all req : RideReq | req.origin != req.dest
    // 2. Each Riding request must be assigned to exactly one Driving driver
    all r : RidingReq | one d : DrivingDriver | r in d.assigned
    all l: Location | some r : Region | l in r.contains
// 

}
run GenerateValidInstance {
    invariants
   #DrivingDriver>1
} for 2
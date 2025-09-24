
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

pred request[r: Rider, req: RideReq,      
             requests_pre, requests_post: Rider -> RideReq, 
             pending_pre, pending_post: set RideReq] {      
    // Pre-condition
    no requests_pre[r]  

    // Post-condition
    req in PendingReq and req not in RidingReq 
    req.rider = r                              

    pending_post = pending_pre + req           
    requests_post = requests_pre + (r -> req)  
}

pred match[req: PendingReq, d: Available,
           assigned_pre, assigned_post: Driver -> RidingReq,
           pending_pre, pending_post: set RideReq,
           riding_pre, riding_post: set RideReq,
           available_pre, available_post: set Driver,
           driving_pre, driving_post: set Driver] {

    // Pre-conditions
    req.origin in d.operatesIn.contains
    req.dest in d.operatesIn.contains

    // Post-conditions (joined with 'and')
    pending_post = pending_pre - req
    and
    riding_post = riding_pre + req
    and
    available_post = available_pre - d
    and
    driving_post = driving_pre + d
    and
    assigned_post = assigned_pre + (d -> req)
}
pred complete[req: RidingReq, d: DrivingDriver,
              requests_pre, requests_post: Rider -> RideReq,
              assigned_pre, assigned_post: Driver -> RidingReq,
              riding_pre, riding_post: set RideReq,
              available_pre, available_post: set Driver,
              driving_pre, driving_post: set Driver] {
    // Pre-condition
    d.assigned = req

    // Post-conditions (joined with 'and')
    riding_post = riding_pre - req
    and
    requests_post = requests_pre - (req.rider -> req)
    and
    driving_post = driving_pre - d
    and
    available_post = available_pre + d  // <-- Corrected line
    and
    assigned_post = assigned_pre - (d -> req)
}

run GenerateValidInstance {
    invariants
   #DrivingDriver>1
} for 2
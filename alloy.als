// --- Core entities ---
sig Rider {
  request : lone RideReq,       // each rider has at most one active request
  assignedTo : set Region       // regions the rider belongs to
}

sig Driver {
  state : one DriverState,      // must always be in exactly one state
  regions : set Region          // regions driver is willing to serve
}

abstract sig DriverState {}
one sig Available, Driving, Offline extends DriverState {}

sig Region {
  contains : some Location
}

sig Location {}

// --- Ride Requests ---
sig RideReq {
  origin : one Location,
  dest   : one Location,
  rider  : one Rider,
  status : one RideStatus,
  driver : lone Driver           // driver matched (none until matched)
}

abstract sig RideStatus {}
one sig Pending, Riding extends RideStatus {}


// --- Invariants ---
pred invariants {
  // 1. Each rider has at most one active request
  all r : Rider | lone r.request

  // 2. A rider’s request must point back to the same rider
  all req : RideReq | req.rider.request = req

  // 3. A request’s origin and destination must be different
  all req : RideReq | req.origin != req.dest

  // 4. If a request is Riding, then it must have a driver assigned and that driver is Driving
  all req : RideReq |
    (req.status = Riding implies (some req.driver and req.driver.state = Driving))

  // 5. If a driver is Driving, then they must be assigned to at least one request with status Riding
  all d : Driver |
    (d.state = Driving implies some req : RideReq | req.driver = d and req.status = Riding)

  // 6. If a request is Pending, then its driver must be none
  all req : RideReq | (req.status = Pending implies no req.driver)

  // 7. Drivers cannot require themselves (region sanity: not needed here, but included as check)
  // all d : Driver | d not in d.regions

  // 8. Request within driver’s regions: origin and destination must be in driver’s regions
  all req : RideReq |
    some req.driver implies (
      req.origin in (req.driver.regions.contains) and
      req.dest in (req.driver.regions.contains)
    )

  // Every location is contained in exactly one region
  all l : Location | one r : Region | l in r.contains

  // If there's an avail
}


// --- Run command ---
run GenerateValidInstance {
  invariants
  some Rider
  some Driver
  some RideReq
} for 2

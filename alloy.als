sig Presto {
	available_drivers: set Driver,
	offline_drivers: set Driver,
	driving_drivers: set Driver,

	pending_requests: set Request,
	riding_requests: set Request,
	
	/*
		p.rider_assignments[Rider] -> gets the range of rider_assignments
		p.rider_assignments.univ -> gets the domain of rider_assignments
	*/

	// these are partial injective functions
	// at most one active request per rider
	rider_assignments: Rider lone -> lone Request,
	// each driving driver is assigned to exactly one ride request
	driver_assignments: Driver lone -> lone Request
}

sig Rider {}

abstract sig Driver {
	operating_regions: some Region
}

sig Region {}
sig Location {
	parent_region: one Region
}

abstract sig Request {
	origin: one Location,
	dest: one Location,
}


pred invariants[p: Presto] {
	// driver statuses are mutually exclusive
	p.available_drivers & p.offline_drivers = none
	p.offline_drivers & p.driving_drivers = none
	p.driving_drivers & p.available_drivers = none

	// pending and riding requests are mutually exclusive
	p.pending_requests & p.riding_requests = none

	// every request that is referenced by a rider assignment must be in either pending or riding requests
	p.rider_assignments[Rider] = p.pending_requests + p.riding_requests

	// every request that is referenced by a driver assignment must be a riding request
	p.driver_assignments[Driver] = p.riding_requests

	// every driver that is referenced by driver assignment must be driving
	p.driver_assignments.univ = p.driving_drivers
}


fact {
	// uninteresting invariants that apply globally

	// every region must have one location
	all r: Region | some l: Location | r in l.parent_region
	// all requests must have different origin and destination
	all req: Request | req.origin != req.dest
	
	// all drivers are tracked in all Presto instances
	// since all presto instances are really the just same, just at different times
	all p: Presto, d: Driver | d in p.available_drivers + p.offline_drivers + p.driving_drivers
}


pred op_request[p1, p2 : Presto, r : Rider, req : Request] {
	// pre:
	// this request cannot already be pending nor riding
	req not in p1.pending_requests + p1.riding_requests
	// this rider is not assigned to this request
	(r -> req) not in p1.rider_assignments

	// post:
	// rider now holds the request
	p2.rider_assignments = p1.rider_assignments + (r -> req)
	// add req to pending_request set
	p2.pending_requests = p1.pending_requests + req

	// everything else unchanged
	p2.available_drivers = p1.available_drivers
	p2.offline_drivers = p1.offline_drivers
	p2.driving_drivers = p1.driving_drivers
	p2.riding_requests = p1.riding_requests
	p2.driver_assignments = p1.driver_assignments
}

pred op_cancel[p1, p2 : Presto, r : Rider] {
	let req = p1.rider_assignments[r] | {
		// pre:
		// rider's request exists and is pending
		req != none
		req in p1.pending_requests	
		
		// post:
		// unassign the rider and remove from pending
		p2.rider_assignments = p1.rider_assignments - (r -> req)
		p2.pending_requests = p1.pending_requests - req
	
		// everything else unchanged
		p2.available_drivers = p1.available_drivers
		p2.offline_drivers = p1.offline_drivers
		p2.driving_drivers = p1.driving_drivers
		p2.riding_requests = p1.riding_requests
		p2.driver_assignments = p1.driver_assignments
	}
}


pred op_match[p1, p2 : Presto, r : Rider, d : Driver] {
	let req = p1.rider_assignments[r] | {
		// pre:
		// rider's request exists and is pending
		req != none
		req in p1.pending_requests

		// driver must be available
		d in p1.available_drivers
		
		// if there's any driver (d2) that operates in the request's origin region
		// then the driver we're trying to match (d) must operate in the request's origin region
		(some d2: Driver | req.origin.parent_region in d2.operating_regions)
			implies req.origin.parent_region in d.operating_regions
		
		
		// post:
		// move request from pending to riding
		p2.pending_requests = p1.pending_requests - req
		p2.riding_requests = p1.riding_requests + req
		// assign the driver
		p2.driver_assignments = p1.driver_assignments + (d -> req)
		p2.available_drivers = p1.available_drivers - d
		p2.driving_drivers = p1.driving_drivers + d

		// everything else unchanged
		p2.offline_drivers = p1.offline_drivers
		p2.rider_assignments = p1.rider_assignments
	}
}


pred op_complete[p1, p2 : Presto, r : Rider, d : Driver] {
	let req1 = p1.rider_assignments[r], req2 = p1.driver_assignments[d] | {
		// pre:	
		// rider and driver are assigned to the same request
		req1 = req2
		// request exists
		req1 != none

		
		// post:
		// remove the request
		p2.riding_requests = p1.riding_requests - req1
		p2.rider_assignments = p1.rider_assignments - (r -> req1)
		p2.driver_assignments = p1.driver_assignments - (d -> req1)
		
		// make driver available
		p2.driving_drivers = p1.driving_drivers - d
		p2.available_drivers = p1.available_drivers + d

		// everything else unchanged
		p2.offline_drivers = p1.offline_drivers
		p2.pending_requests = p1.pending_requests
	}
}


assert RequestPreservesInvariants {
	all p1, p2: Presto, r: Rider, req: Request |
		invariants[p1] and op_request[p1, p2, r, req] implies invariants[p2]
}

assert CancelPreservesInvariants {
	all p1, p2: Presto, r: Rider |
		invariants[p1] and op_cancel[p1, p2, r] implies invariants[p2]
}

assert MatchPreservesInvariants {
	all p1, p2: Presto, r: Rider, d: Driver |
		invariants[p1] and op_match[p1, p2, r, d] implies invariants[p2]
}

assert CompletePreservesInvariants {
	all p1, p2: Presto, r: Rider, d: Driver |
		invariants[p1] and op_complete[p1, p2, r, d] implies invariants[p2]
}

check RequestPreservesInvariants
for 6 but
exactly 2 Presto

check CancelPreservesInvariants
for 6 but
exactly 2 Presto

check MatchPreservesInvariants
for 6 but
exactly 2 Presto

check CompletePreservesInvariants
for 6 but
exactly 2 Presto

run GenerateValidRequest {
	all p: Presto | invariants[p]
	some p1, p2: Presto, r: Rider, req: Request |
		op_request[p1, p2, r, req]
}
for
exactly 1 Region,
exactly 2 Location,
exactly 0 Driver,
exactly 2 Presto,
exactly 2 Request,
exactly 2 Rider

run GenerateValidCancel {
	all p: Presto | invariants[p]
	some p1, p2: Presto, r: Rider |
		op_cancel[p1, p2, r]
}
for
exactly 1 Region,
exactly 2 Location,
exactly 0 Driver,
exactly 2 Presto,
exactly 2 Request,
exactly 2 Rider

run GenerateValidMatch {
	all p: Presto | invariants[p]
	some p1, p2: Presto, r: Rider, d: Driver |
		op_match[p1, p2, r, d]

	// no offline drivers (not interesting)
	all p: Presto | p.offline_drivers = none
	// one region should have no operating drivers
	// since we want to see what happens if the request origin is a location with no drivers
	some r: Region | no d: Driver | r in d.operating_regions
}
for
exactly 2 Region,
exactly 4 Location,
exactly 2 Driver,
exactly 2 Presto,
exactly 1 Request,
exactly 1 Rider


run GenerateValidComplete {
	all p: Presto | invariants[p]
	some p1, p2: Presto, r: Rider, d: Driver |
		op_complete[p1, p2, r, d]

	// no offline drivers (not interesting)
	all p: Presto | p.offline_drivers = none
}
for
exactly 2 Region,
exactly 4 Location,
exactly 2 Driver,
exactly 2 Presto,
exactly 1 Request,
exactly 1 Rider

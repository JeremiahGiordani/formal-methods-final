
// ###############
// Object Definitions
// ###############

abstract sig User {} 

sig Rider extends User {} 

abstract sig Driver extends User { 
	operatesIn: set Region 
} 

sig OfflineDriver extends Driver {} 
sig OnlineDriver extends Driver {} 

sig Region {} 
sig Location { 
	locatedIn: one Region 
} 

sig Request { 
	origin: one Location,
	destination: one Location, 
	requestedBy: one Rider
}


// ###############
// State
// ###############

sig Presto {
	active: some Request,
	matchedTo: Request -> lone OnlineDriver,
	queue: seq Request
}


// ###############
// Invariants
// ###############

pred invariants [p: Presto] {
	// Global Invariants:
	
	// Rider can only have a single request.
	all r: Rider | lone requestedBy.r

	// Request origin and destination cannot be the same.
	all r : Request | r.origin != r.destination

	// State invariants

	// Drivers can only match to a single request.
	all d : OnlineDriver | lone (p.matchedTo).d

	// Presto atom can only match drivers to active requests.
	all r: Request | some p.matchedTo[r] implies r in p.active

	// Elements in queue must be in active requests
	p.queue.elems in p.active

	// No cycles in queue
	not p.queue.hasDups

	// Requests are in the queue if and only if the request is pending
	all r: p.active | no p.matchedTo[r] iff r in p.queue.elems
}

// ###############
// Operations
// ###############

// ### Request ###

pred request[s1, s2: Presto, r: Rider, req: Request] {
	// Pre-conditions:
	// New request is not in s1 active requests.
	req not in s1.active

	// Rider does not have a current active request.
	r not in s1.active.requestedBy

	// Given rider made given request. 
	req.requestedBy = r

	// Post-condition:
	s2.active = s1.active + req
	s2.matchedTo = s1.matchedTo
	s2.queue = s1.queue.add[req]
}

// ### Cancel ###

pred cancel[s1, s2: Presto, r: Rider] {
	// Pre-conditions:
	// Rider must have a request.
	some requestedBy.r

	// Rider's request must be in active requests
	 requestedBy.r in s1.active

	// Request must not be matched
	no s1.matchedTo[requestedBy.r]

	// Post-condition:
	s2.active = s1.active - requestedBy.r
	s2.matchedTo = s1.matchedTo
	s2.queue = s1.queue.delete[s1.queue.idxOf[requestedBy.r]]
}

// ### Match ###

pred availableDriverInRegion[s: Presto, req: Request] {
	// Predicate to determine if there exists an
	// available driver in the request region.
	
	// There exists some driver such that:
	some d: OnlineDriver | 
		// they are not matched to a request, and
		no s.matchedTo.d and
		// they operate in the request origin, and 
		req.origin.locatedIn in d.operatesIn and
		// they operate in the request destination 
		req.destination.locatedIn in d.operatesIn
}

pred currentDriverInRegion[s: Presto, req: Request, d:Driver] {
	// Predicate to determine if the specified driver
	// operates in the request region
	
	req.origin.locatedIn in d.operatesIn and
	req.destination.locatedIn in d.operatesIn
}

pred match[s1, s2: Presto, r: Rider, d: Driver] {
	// Pre-conditions:
	// Rider must have a request.
	some requestedBy.r

	// Rider's request must be in active requests
	 requestedBy.r in s1.active

	// Request must not be matched
	no s1.matchedTo[requestedBy.r]

	// Driver must be online
	d in OnlineDriver

	// Driver must not be matched
	no s1.matchedTo.d

	// Request must be the earliest pending request.
	s1.queue.first = requestedBy.r

	// Driver can only take the ride if they operate in the 
	// request area, or there are no available drivers in the area
	not currentDriverInRegion[s1, requestedBy.r, d] implies 
	not availableDriverInRegion[s1, requestedBy.r]
		
	// Post-condition:
	s2.active = s1.active
	s2.matchedTo = s1.matchedTo + requestedBy.r -> d
	s2.queue = s1.queue.rest
}

// ### Complete ###

pred complete[s1, s2: Presto, r: Rider, d: Driver] {
	// Pre-conditions:
	// Rider must have a request.
	some requestedBy.r

	// Rider's request must be in active requests
	 requestedBy.r in s1.active

	// Rider and Driver must be Matched
	d = s1.matchedTo[requestedBy.r]
	requestedBy.r -> d in s1.matchedTo

	// Post-condition:
	s2.active = s1.active - requestedBy.r
	s2.matchedTo = s1.matchedTo - requestedBy.r -> d
	s2.queue = s1.queue
}


// ###############
// Show
// ###############

pred showConditions {
	//all r: Request | no Presto.matchedTo[r]
	all d: OfflineDriver | d.operatesIn = Region
	some d: OnlineDriver | d.operatesIn = Region
	some d: OnlineDriver | no d.operatesIn
	some p:Presto | no p.matchedTo
}

pred show{
	all p: Presto | invariants[p] 
}

// ### Request ###

pred showRequest {
	some s1, s2: Presto, r: Rider, req: Request |
    		invariants[s1] and request[s1, s2, r, req]
	// side conditions
	and showConditions	
}

// ### Cancel ###

pred showCancel {
	some s1, s2: Presto, r: Rider |
    		invariants[s1] and cancel[s1, s2, r]
	// side conditions
	and showConditions	
}

// ### Match ###

pred showMatch {
	some s1, s2: Presto, r: Rider, d: Driver |
    		invariants[s1] and match[s1, s2, r, d]
	// side conditions
	and showConditions	
}

// ### Complete ###

pred showComplete {
	some s1, s2: Presto, r: Rider, d: Driver |
    		invariants[s1] and complete[s1, s2, r, d]
	// side conditions
	and showConditions	
}

// ### Request then Cancel ###

pred showRequestThenCancel {
	some s1, s2, s3: Presto, r: Rider, req: Request |
		invariants[s1] and 
		request[s1, s2, r, req] and
		cancel[s2, s3, r]
	// side conditions
	and showConditions	
}

// ### Request then Match ###

pred showRequestThenMatch {
	some s1, s2, s3: Presto, r: Rider, req: Request, d:Driver |
		invariants[s1] and 
		request[s1, s2, r, req] and
		match[s2, s3, r, d]
	// side conditions
	and showConditions	
}

pred showMatchThenComplete {
	some s1, s2,s3: Presto, r: Rider,d:Driver |
		invariants[s1] and
		match[s1, s2, r,d] and
		complete[s2,s3,r,d]
	// side conditions
	and showConditions	
}


// ###############
// Asserts
// ###############


// ###############
// ### Request ###

pred RequestPreservesInvariants {
	all s1, s2: Presto, r: Rider, req: Request |
		invariants[s1] and request[s1, s2, r, req] implies invariants[s2]

}

pred RequestIncreasesActiveAndRetainsMatch{
	all s1, s2: Presto, r: Rider, req: Request |
		invariants[s1] and request[s1, s2, r, req] implies 
		#(s1.active) <  #(s2.active) and
		s1.matchedTo = s2.matchedTo
}

assert RequestAsserts {
	RequestPreservesInvariants and
	RequestIncreasesActiveAndRetainsMatch 
}

// ###############
// ### Cancel ###

pred CancelPreservesInvariants {
	all s1, s2: Presto, r: Rider |
		invariants[s1] and cancel[s1, s2, r] implies invariants[s2]
}

pred CancelDecreasesActiveAndRetainsMatch{
	all s1, s2: Presto, r: Rider |
		invariants[s1] and cancel[s1, s2, r] implies 
		#(s1.active) >  #(s2.active) and
		s1.matchedTo = s2.matchedTo
}

assert CancelAsserts {
	CancelPreservesInvariants and
	CancelDecreasesActiveAndRetainsMatch
}

// ###############
// ### Match ###

pred MatchPreservesInvariants {
	all s1, s2: Presto, r: Rider, d:Driver |
		invariants[s1] and match[s1, s2, r, d] implies invariants[s2]
}

pred MatchRetainsActiveAndIncreasesMatch{
	all s1, s2: Presto, r: Rider, d:Driver |
		invariants[s1] and match[s1, s2, r,d] implies 
		#(s1.matchedTo) < #(s2.matchedTo) and
		s1.active = s2.active
}

assert MatchAsserts {
	MatchPreservesInvariants and
	MatchRetainsActiveAndIncreasesMatch
}

// ###############
// ### Complete ###

pred CompletePreservesInvariants {
	all s1, s2: Presto, r: Rider, d:Driver |
		invariants[s1] and complete[s1, s2, r, d] implies invariants[s2]
}

pred CompleteDecreasesActiveAndDecreasesMatch{
	all s1, s2: Presto, r: Rider, d:Driver |
		invariants[s1] and complete[s1, s2, r,d] implies 
		#(s1.matchedTo) > #(s2.matchedTo) and
		#(s1.active - requestedBy.r) = #(s2.active)
}

assert CompleteAsserts {
	CompletePreservesInvariants and
	CompleteDecreasesActiveAndDecreasesMatch
}

// ###############
// ### Operation Interaction ###

assert RequestThenCancelIsUndo {
	all s1, s2,s3: Presto, r: Rider, req: Request |
		invariants[s1] and 
		request[s1, s2, r, req] and
		cancel[s2, s3, r] implies
		s1.matchedTo = s3.matchedTo and
		s1.active = s3.active and
		s1.queue = s3.queue
}

assert RequestTwiceThenCancelTwiceIsUndo {
	all s1, s2,s3, s4, s5: Presto, r1, r2: Rider, req1, req2: Request |
		invariants[s1] and 
		request[s1, s2, r1, req1] and
		request[s2, s3, r2, req2] and
		cancel[s3, s4, r2] and
		cancel[s4, s5, r1] implies 
		s1.matchedTo = s5.matchedTo and
		s1.active = s5.active and
		s1.queue = s5.queue
}

assert RequestThenMatchThenCompleteIsUndo {
	all s1, s2,s3,s4: Presto, r: Rider, req: Request,d:Driver |
		invariants[s1] and
		request[s1, s2, r, req] and
		match[s2, s3, r,d] and
		complete[s3,s4,r,d] implies
		s1.matchedTo = s4.matchedTo and
		s1.active = s4.active and
		s1.queue = s4.queue
}

assert MatchThenCompleteImpliesCancel {
	all s1, s2,s3: Presto, r: Rider,d:Driver |
		invariants[s1] and
		match[s1, s2, r,d] and
		complete[s2,s3,r,d] implies
		cancel[s1,s3,r]
}

assert RiderCannotRequestTwice {
	no s1, s2, s3: Presto, r: Rider, req1, req2: Request |
		invariants[s1] and 
		request[s1, s2, r, req1] and
		request[s2, s3, r, req2]
}

assert MatchResolvesFalseWhenNoAvailableDrivers {
	no s1, s2: Presto, r: Rider, d: Driver |
		some s1.matchedTo.d and
		match[s1, s2, r, d]
}

//assert Request


// ###############
// Commands
// ###############

// ### Run ###

//run {show} for 4 but exactly 1 Presto
//run {showRequest} for 4 but exactly 2 Presto
//run {showCancel} for 4 but exactly 2 Presto
//run {showMatch} for 5 but exactly 2 Presto
//run {showComplete} for 5 but exactly 2 Presto

//run {showRequestThenCancel} for 3 but exactly 2 Presto
//run {showRequestThenMatch} for 4 but exactly 3 Presto
//run {showMatchThenComplete} for 4 but exactly 3 Presto


// ### Check ###

// ### Operations ###
//check RequestAsserts for 5 but exactly 2 Presto
//check CancelAsserts for 5 but exactly 2 Presto
//check MatchAsserts for 5 but exactly 2 Presto
//check CompleteAsserts for 5 but exactly 2 Presto

// ### Interactions ###
//check RequestThenCancelIsUndo for 5 but exactly 3 Presto
//check RequestThenMatchThenCompleteIsUndo for 6 but exactly 4 Presto
//check MatchThenCompleteImpliesCancel for 6 but exactly 3 Presto
//check RequestTwiceThenCancelTwiceIsUndo for 6
//check RiderCannotRequestTwice for 3 but exactly 2 Presto
//check MatchResolvesFalseWhenNoAvailableDrivers for 6 but exactly 2 Presto






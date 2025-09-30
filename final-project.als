
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
	matchedTo: Request -> lone OnlineDriver
}


// ###############
// Invariants
// ###############

pred prestoInvariants [p: Presto] {
	// User can only have a single request.
	all u : User | lone requestedBy.u

	// Drivers can only match to a single request.
	all d : OnlineDriver | lone (p.matchedTo).d

	// Presto atom can only match drivers to active requests.
	//p.active + p.matchedTo = p.active
	all r: Request | some p.matchedTo[r] implies r in p.active

}

pred invariants {
	all p : Presto | prestoInvariants[p]
	
	// Request origin and destination cannot be the same.
	all r : Request | r.origin != r.destination
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
}

// ### Match ###

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

	// Post-condition:
	s2.active = s1.active
	s2.matchedTo = s1.matchedTo + requestedBy.r -> d
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
}


// ###############
// Show
// ###############

pred showConditions {
	//all r : Request | some active.r
	invariants
	
}

// ### Request ###

pred showRequest {
	some s1, s2: Presto, r: Rider, req: Request |
    		request[s1, s2, r, req]
	// side conditions
	and showConditions	
}

// ### Cancel ###

pred showCancel {
	some s1, s2: Presto, r: Rider |
    		cancel[s1, s2, r]
	// side conditions
	and showConditions	
}

// ### Match ###

pred showMatch {
	some s1, s2: Presto, r: Rider, d: Driver |
    		match[s1, s2, r, d]
	// side conditions
	and showConditions	
}

// ### Complete ###

pred showComplete {
	some s1, s2: Presto, r: Rider, d: Driver |
    		complete[s1, s2, r, d]
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
		invariants and request[s1, s2, r, req] implies invariants

}

pred RequestIncreasesActiveAndRetainsMatch{
	all s1, s2: Presto, r: Rider, req: Request |
		invariants and request[s1, s2, r, req] implies 
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
		invariants and cancel[s1, s2, r] implies invariants
}

pred CancelDecreasesActiveAndRetainsMatch{
	all s1, s2: Presto, r: Rider |
		invariants and cancel[s1, s2, r] implies 
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
		invariants and match[s1, s2, r, d] implies invariants
}

pred MatchRetainsActiveAndIncreasesMatch{
	all s1, s2: Presto, r: Rider, d:Driver |
		invariants and match[s1, s2, r,d] implies 
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
		invariants and complete[s1, s2, r, d] implies invariants
}

pred CompleteDecreasesActiveAndDecreasesMatch{
	all s1, s2: Presto, r: Rider, d:Driver |
		invariants and complete[s1, s2, r,d] implies 
		#(s1.matchedTo) > #(s2.matchedTo) and
		#(s1.active - requestedBy.r) = #(s2.active)
}

assert CompleteAsserts {
	CompletePreservesInvariants and
	CompleteDecreasesActiveAndDecreasesMatch
}

// ###############
// ### Operation Interaction ###

assert RequestThenCancelUndo {
	all s1, s2,s3: Presto, r: Rider, req: Request |
		request[s1, s2, r, req] and
		cancel[s2, s3, r] implies
		s1.matchedTo = s3.matchedTo and
		s1.active = s3.active
}

assert RequestThenMatchThenCompleteIsUndo {
	all s1, s2,s3,s4: Presto, r: Rider, req: Request,d:Driver |
		invariants and
		request[s1, s2, r, req] and
		match[s2, s3, r,d] and
		complete[s3,s4,r,d] implies
		s1.matchedTo = s4.matchedTo and
		s1.active = s4.active
}

assert MatchThenCompleteImpliesCancel {
	all s1, s2,s3: Presto, r: Rider,d:Driver |
		invariants and
		match[s1, s2, r,d] and
		complete[s2,s3,r,d] implies
		cancel[s1,s3,r]
}


// ###############
// Commands
// ###############

// ### Assert ###

run {showRequest} for 4 but exactly 2 Presto
//run {showCancel} for 4 but exactly 2 Presto
//run {showMatch} for 5 but exactly 2 Presto
//run {showComplete} for 5 but exactly 2 Presto


// ### Check ###

// ### Operations ###
//check RequestAsserts for 5 but exactly 2 Presto
//check CancelAsserts for 5 but exactly 2 Presto
//check MatchAsserts for 5 but exactly 2 Presto
//check CompleteAsserts for 5 but exactly 2 Presto

// ### Interactions ###
//check RequestThenCancelUndo for 5 but exactly 3 Presto
//check RequestThenMatchThenCompleteIsUndo for 4 but exactly 4 Presto
//check MatchThenCompleteImpliesCancel for 3 but exactly 3 Presto





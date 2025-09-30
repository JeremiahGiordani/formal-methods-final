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

sig Presto { 
	active: some Request,
	matchedTo: Request -> lone OnlineDriver
} 

pred invariants [p: Presto] {
	// User can only have a single request.
	all u : User | lone requestedBy.u

	// Drivers can only match to a single request.
	all d : OnlineDriver | lone (p.matchedTo).d

	// Request origin and destination cannot be the same.
	all r : Request | r.origin != r.destination

	// Presto atom can only match drivers to active requests.
	no p

}

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

run {
	some s1, s2: Presto, r: Rider, req: Request |
    		request[s1, s2, r, req]
} for 4 but exactly 2 Presto


//run {
//	all r: Request | some active.r and 
	//all r : Request | #(r.(Presto.matchedTo)) = 1
//	all p: Presto | invariants[p] 
//} for 4 but exactly 1 Presto, exactly 2 Request, exactly 2 OnlineDriver

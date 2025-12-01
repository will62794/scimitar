---- MODULE toy_consensus_forall ----

EXTENDS TLC, Naturals, FiniteSets

CONSTANT Node
CONSTANT Value
CONSTANT Nil

VARIABLE vote
VARIABLE voted
VARIABLE decided

vars == <<vote, voted, decided>>

\* The set of all majority quorums in the Node set.
Quorums == {i \in SUBSET(Node) : Cardinality(i) * 2 > Cardinality(Node)}

\* Node 'i' casts a vote for value 'v'.
CastVote(i, v) == 
    /\ ~voted[i]
    /\ vote' = [vote EXCEPT ![i] = v]
    /\ voted' = [voted EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<decided>>

\* Decide on a value 'v' with quorum 'Q'.
Decide(v, Q) == 
    /\ \A n \in Q : vote[n] = v
    /\ decided' = decided \cup {v}
    /\ UNCHANGED <<vote,voted>>

Init ==
    /\ vote = [n \in Node |-> Nil]
    /\ voted = [n \in Node |-> FALSE]
    /\ decided = {}

CastVoteAction == TRUE /\ \E i \in Node, v \in Value : CastVote(i, v)
DecideAction == TRUE /\ \E v \in Value, Q \in Quorums : Decide(v, Q)

Next == 
    \/ CastVoteAction
    \/ DecideAction

NextUnchanged == UNCHANGED vars

\* Can only decide on a single value
ConsensusInv == \A vi,vj \in decided : vi = vj

TypeOK == 
    /\ vote \in [Node -> Value \cup {Nil}]
    /\ voted \in [Node -> BOOLEAN]
    /\ decided \in SUBSET Value

Symmetry == Permutations(Node)

CTICost == 0

====
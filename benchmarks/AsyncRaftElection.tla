--------------------------------- MODULE AsyncRaftElection ---------------------------------
\* Spec of Raft with message passing.

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS 
    Server

\* Server states.
CONSTANTS 
    Follower, 
    Candidate, 
    Leader

\* A reserved value.
CONSTANTS  Nil

\* Message types:
CONSTANTS 
    RequestVoteRequest, 
    RequestVoteResponse

----

VARIABLE requestVoteRequestMsgs
VARIABLE requestVoteResponseMsgs

\* The server's term number.
VARIABLE currentTerm

\* The server's state (Follower, Candidate, or Leader).
VARIABLE state

\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor

\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE  votesGranted


\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<requestVoteRequestMsgs, requestVoteResponseMsgs, currentTerm, state, votedFor, votesGranted>>

\* Helpers

Min(s) == CHOOSE x \in s : \A y \in s : x <= y
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

IsPrefix(s, t) ==
  (**************************************************************************)
  (* TRUE iff the sequence s is a prefix of the sequence t, s.t.            *)
  (* \E u \in Seq(Range(t)) : t = s \o u. In other words, there exists      *)
  (* a suffix u that with s prepended equals t.                             *)
  (**************************************************************************)
  Len(s) <= Len(t) /\ SubSeq(s, 1, Len(s)) = SubSeq(t, 1, Len(s))
  
----
\* Define initial values for all variables

Init == 
    /\ requestVoteRequestMsgs = {}
    /\ requestVoteResponseMsgs = {}
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Follower]
    /\ votedFor    = [i \in Server |-> Nil]
    /\ votesGranted = [i \in Server |-> {}]
    
----
\* Define state transitions

\* ACTION: RequestVote
\* Combined Timeout and RequestVote of the original spec to reduce
\* state space.
\* Server i times out and starts a new election. 
\* Sends a RequestVote request to all peers but not itself.
RequestVote(i) ==
    /\ state[i] \in {Follower, Candidate}
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i] \* votes for itself
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {i}] \* votes for itself
    /\ requestVoteRequestMsgs' = requestVoteRequestMsgs \cup 
            {[  mtype         |-> RequestVoteRequest,
                mterm         |-> currentTerm[i] + 1,
                msource       |-> i,
                mdest         |-> j] : j \in Server \ {i}}
    /\ UNCHANGED <<requestVoteResponseMsgs>>

\* ACTION: BecomeLeader -------------------------------------------
\* Candidate i transitions to leader.
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ UNCHANGED <<currentTerm, votedFor, votesGranted, requestVoteRequestMsgs, requestVoteResponseMsgs>>

UpdateTerm(mterm,mdest) ==
    /\ mterm > currentTerm[mdest]
    /\ currentTerm'    = [currentTerm EXCEPT ![mdest] = mterm]
    /\ state'          = [state       EXCEPT ![mdest] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![mdest] = Nil]
        \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<votesGranted, requestVoteRequestMsgs, requestVoteResponseMsgs>>


\* ACTION: HandleRequestVoteRequest ------------------------------
\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
\* @type: ({ mtype: Str, mterm: Int, mlastLogTerm: Int, mlastLogIndex: Int, msource: SERVER, mdest: SERVER }) => Bool;
HandleRequestVoteRequest(m) ==
    /\ m \in requestVoteRequestMsgs
    /\ m.mtype = RequestVoteRequest
    /\ m.mterm <= currentTerm[m.mdest]
    /\ LET  i     == m.mdest
            j     == m.msource
            grant == /\ m.mterm = currentTerm[i]
                     /\ votedFor[i] \in {Nil, j} 
                     IN
            /\ votedFor' = [votedFor EXCEPT ![i] = IF grant THEN j ELSE votedFor[i]]
            /\ requestVoteResponseMsgs' = requestVoteResponseMsgs \cup {[
                            mtype        |-> RequestVoteResponse,
                            mterm        |-> currentTerm[i],
                            mvoteGranted |-> grant,
                            msource      |-> i,
                            mdest        |-> j]}
            /\ requestVoteRequestMsgs' = requestVoteRequestMsgs \ {m} \* discard the message.
            /\ UNCHANGED <<state, currentTerm, votesGranted>>

\* ACTION: HandleRequestVoteResponse --------------------------------
\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse(m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m \in requestVoteResponseMsgs
    /\ m.mtype = RequestVoteResponse
    /\ m.mterm = currentTerm[m.mdest]
    /\ votesGranted' = [votesGranted EXCEPT ![m.mdest] = 
                                IF m.mvoteGranted 
                                    THEN votesGranted[m.mdest] \cup {m.msource} 
                                    ELSE votesGranted[m.mdest]]
    /\ requestVoteResponseMsgs' = requestVoteResponseMsgs \ {m} \* discard the message.
    /\ UNCHANGED <<currentTerm, state, votedFor, requestVoteRequestMsgs>>


RequestVoteAction == TRUE /\ \E i \in Server : RequestVote(i)
UpdateTermAction == TRUE /\ \E m \in requestVoteRequestMsgs \cup requestVoteResponseMsgs : UpdateTerm(m.mterm, m.mdest)
BecomeLeaderAction == TRUE /\ \E i \in Server : BecomeLeader(i)
HandleRequestVoteRequestAction == \E m \in requestVoteRequestMsgs : HandleRequestVoteRequest(m)
HandleRequestVoteResponseAction == \E m \in requestVoteResponseMsgs : HandleRequestVoteResponse(m)

\* Defines how the variables may transition.
Next == 
    \/ RequestVoteAction
    \/ UpdateTermAction
    \/ HandleRequestVoteRequestAction
    \/ HandleRequestVoteResponseAction
    \/ BecomeLeaderAction


CONSTANT 
    \* @type: Int;
    MaxTerm

MCSymmetry == Permutations(Server)

StateConstraint == 
    /\ \A s \in Server : currentTerm[s] <= MaxTerm

H_OnePrimaryPerTerm == 
    \A s,t \in Server : 
        (s # t /\ state[s] = Leader /\ state[t] = Leader) => currentTerm[s] # currentTerm[t]

==========
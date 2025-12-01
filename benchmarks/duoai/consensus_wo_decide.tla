---- MODULE consensus_wo_decide ----

EXTENDS TLC, Naturals

CONSTANT Node
CONSTANT Quorums

VARIABLE vote_request_msg
VARIABLE voted
VARIABLE vote_msg
VARIABLE votes
VARIABLE leader
VARIABLE voting_quorum

SendRequestVote(i,j) == 
    /\ vote_request_msg' = [vote_request_msg EXCEPT ![<<i,j>>] = TRUE]
    /\ UNCHANGED <<voted, vote_msg, votes, leader, voting_quorum>>

SendVote(src,dst)==
    /\ ~voted[src]
    /\ vote_request_msg[<<dst,src>>]
    /\ vote_msg' = [vote_msg EXCEPT ![<<src,dst>>] = TRUE]
    /\ voted' = [voted EXCEPT ![src] = TRUE]
    /\ UNCHANGED <<vote_request_msg, votes, leader, voting_quorum>>

RecvVote(i,sender)==
    /\ vote_msg[<<sender,i>>]
    /\ votes' = [votes EXCEPT ![<<i,sender>>] = TRUE]
    /\ UNCHANGED <<vote_request_msg, vote_msg, voted, leader, voting_quorum>>

ChooseVotingQuorum(i) ==
    \E Q \in Quorums :
    /\ \A v \in Q : votes[<<i,v>>]
    /\ voting_quorum' = Q
    /\ UNCHANGED <<vote_request_msg, vote_msg, votes, voted, leader>>

BecomeLeader(i) == 
    /\ voting_quorum # {}
    /\ \A v \in voting_quorum : votes[<<i,v>>]
    /\ leader' = [leader EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<vote_request_msg, vote_msg, voted, votes, voting_quorum>>

Init == 
    /\ vote_request_msg = [s \in Node \X Node |-> FALSE]
    /\ voted = [s \in Node |-> FALSE]
    /\ vote_msg = [s \in Node \X Node |-> FALSE]
    /\ votes = [s \in Node \X Node |-> FALSE]
    /\ leader = [s \in Node |-> FALSE]
    /\ voting_quorum \in Quorums

SendRequestVoteAction == TRUE /\ \E i,j \in Node : SendRequestVote(i,j)
SendVoteAction == TRUE /\ \E i,j \in Node : SendVote(i,j)
RecvVoteAction == TRUE /\ \E i,j \in Node : RecvVote(i,j)
ChooseVotingQuorumAction == TRUE /\ \E i \in Node : ChooseVotingQuorum(i)
BecomeLeaderAction == TRUE /\ \E i \in Node : BecomeLeader(i)

Next == 
    \/ SendRequestVoteAction
    \/ SendVoteAction
    \/ RecvVoteAction
    \/ ChooseVotingQuorumAction
    \/ BecomeLeaderAction

TypeOK == 
    /\ vote_request_msg \in [Node \X Node -> BOOLEAN]
    /\ voted \in [Node -> BOOLEAN]
    /\ vote_msg \in [Node \X Node -> BOOLEAN]
    /\ votes \in [Node \X Node -> BOOLEAN]
    /\ leader \in [Node -> BOOLEAN]
    /\ voting_quorum \in Quorums

\* TypeOKRandom ==
\*     /\ vote_request_msg \in RandomSubset(25, [Node \X Node -> BOOLEAN])
\*     /\ voted \in RandomSubset(6, [Node -> BOOLEAN])
\*     /\ vote_msg \in RandomSubset(25, [Node \X Node -> BOOLEAN])
\*     /\ votes \in RandomSubset(25, [Node \X Node -> BOOLEAN])
\*     /\ leader \in RandomSubset(6, [Node -> BOOLEAN])
\*     /\ voting_quorum \in RandomSubset(4, Quorums)

ConsensusInv == \A i,j \in Node : (leader[i] /\ leader[j]) => (i = j)

NoLeader == ~\E i \in Node : leader[i]

Symmetry == Permutations(Node)

NextUnchanged == UNCHANGED <<vote_request_msg,voted,vote_msg,votes,leader,voting_quorum>>

CTICost == 0

====
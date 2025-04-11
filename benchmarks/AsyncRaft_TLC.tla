--------------------------------- MODULE AsyncRaft_TLC ---------------------------------
EXTENDS AsyncRaft, Randomization



\* Set of all subsets of a set of size <= k.
\* kOrSmallerSubset(k, S) == UNION {(kSubset(n, S)) : n \in 0..k}

\* 
\* Work around size limitations of TLC subset computations.
\* 

\* RequestVoteResponseTypeSampled == UNION { kOrSmallerSubset(2, RequestVoteResponseTypeOp({t})) : t \in Terms }
\* RequestVoteRequestTypeSampled == UNION { kOrSmallerSubset(2, RequestVoteRequestTypeOp({t})) : t \in Terms }


\* Terms == 0..MaxTerm
\* LogIndices == 1..MaxLogLen
\* LogIndicesWithZero == 0..MaxLogLen

\* Symmetry == Permutations(Server)

\* \* In this spec we send at most 1 log entry per AppendEntries message. 
\* \* We encode this in the type invariant for convenience.
\* MaxMEntriesLen == 1


RequestVoteRequestTypeBounded == [
    mtype         : {RequestVoteRequest},
    mterm         : Terms,
    \* mlastLogTerm  : Terms,
    \* mlastLogIndex : LogIndicesWithZero,
    mlog          : BoundedSeq(Terms, MaxMEntriesLen),
    msource       : Server,
    mdest         : Server
]

RequestVoteResponseTypeBounded == [
    mtype        : {RequestVoteResponse},
    mterm        : Terms,
    mvoteGranted : BOOLEAN,
    msource      : Server,
    mdest        : Server
]

AppendEntriesRequestTypeBounded == [
    mtype      : {AppendEntriesRequest},
    mterm      : Terms,
    mprevLogIndex  : LogIndices,
    mprevLogTerm   : Terms,
    mentries       : BoundedSeq(Terms, MaxMEntriesLen),
    mcommitIndex   : LogIndicesWithZero,
    msource        : Server,
    mdest          : Server
]

AppendEntriesResponseTypeBounded == [
    mtype        : {AppendEntriesResponse},
    mterm        : Terms,
    msuccess     : BOOLEAN,
    mmatchIndex  : LogIndices,
    msource      : Server,
    mdest        : Server
]

AvgSubsetSize == 1
NumSubsets == 15

\* RequestVoteRequestTypeSampled == RandomSetOfSubsets(NumSubsets, AvgSubsetSize, RequestVoteRequestTypeBounded) 
\* RequestVoteResponseTypeSampled == RandomSetOfSubsets(NumSubsets, AvgSubsetSize, RequestVoteResponseTypeBounded)  
\* AppendEntriesRequestTypeSampled == RandomSetOfSubsets(10, 1, AppendEntriesRequestTypeBounded) \*\cup RandomSetOfSubsets(3, 3, AppendEntriesRequestTypeBounded)
\* AppendEntriesResponseTypeSampled == RandomSetOfSubsets(10, 1, AppendEntriesResponseTypeBounded) \*\cup RandomSetOfSubsets(2, 2, AppendEntriesResponseTypeBounded) \cup RandomSetOfSubsets(3, 3, AppendEntriesResponseTypeBounded)  

\* Assume max of 1 message in network is sufficient for CTI sampling.
RequestVoteRequestTypeSampled == {{m,m1} : m,m1 \in RandomSubset(80, RequestVoteRequestTypeBounded)}
RequestVoteResponseTypeSampled == {{m,m1} : m,m1 \in RandomSubset(80, RequestVoteResponseTypeBounded)}
AppendEntriesRequestTypeSampled == {{m,m1} : m,m1 \in RandomSubset(80, AppendEntriesRequestTypeBounded)}
AppendEntriesResponseTypeSampled == {{m,m1} : m,m1 \in RandomSubset(80, AppendEntriesResponseTypeBounded)}

TypeOKRandom == 
    /\ requestVoteRequestMsgs \in RequestVoteRequestTypeSampled
    /\ requestVoteResponseMsgs \in RequestVoteResponseTypeSampled 
    /\ appendEntriesRequestMsgs \in AppendEntriesRequestTypeSampled
    /\ appendEntriesResponseMsgs \in AppendEntriesResponseTypeSampled
    /\ currentTerm \in [Server -> Terms]
    /\ state       \in [Server -> {Leader, Follower, Candidate}]
    /\ votedFor    \in [Server -> ({Nil} \cup Server)]
    /\ votesGranted \in [Server -> (SUBSET Server)]
    /\ log             \in [Server -> BoundedSeq(Terms, MaxLogLen)]
    /\ commitIndex     \in [Server -> LogIndicesWithZero]
    /\ nextIndex  \in [Server -> RandomSubset(8, [Server -> LogIndices])]
    /\ matchIndex \in [Server -> RandomSubset(8, [Server -> LogIndicesWithZero])]   

Symmetry == Permutations(Server)

\* Sum the elements in the range of a function.
RECURSIVE SumFnRange(_)
SumFnRange(f) == IF DOMAIN f = {} THEN 0 ELSE
  LET x == CHOOSE x \in DOMAIN f : TRUE
    IN f[x] + SumFnRange([k \in (DOMAIN f) \ {x} |-> f[k]])

CTICost == 0
    \* SumFnRange([s \in Server |-> Cardinality(votesGranted[s])]) +
    \* SumFnRange([s \in Server |-> Len(log[s])]) +
    \* SumFnRange(currentTerm) + 
    \* SumFnRange(commitIndex) + 
    \* Cardinality(requestVoteRequestMsgs \cup requestVoteResponseMsgs) + 
    \* Cardinality(appendEntriesRequestMsgs \cup appendEntriesResponseMsgs) + 
    \* SumFnRange([s \in Server |-> IF state[s] \in {Follower,Candidate} THEN 0 ELSE 1])


===============================================================================
--------------------------------- MODULE AsyncRaft_IndProofs_nfm ---------------------------------
EXTENDS AsyncRaft,TLAPS,FiniteSetTheorems

LEMMA QuorumsExistForNonEmptySets ==
ASSUME NEW S, IsFiniteSet(S), S # {}
PROVE Quorum # {}
PROOF BY FS_EmptySet, FS_CardinalityType DEF Quorum

LEMMA QuorumsAreServerSubsets ==
ASSUME TypeOK, NEW s \in Server
PROVE Quorum \subseteq SUBSET Server
PROOF BY DEF Quorum, TypeOK

LEMMA AddingToQuorumRemainsQuorum == \A Q \in Quorum : \A s \in Server : Q \in Quorum => Q \cup {s} \in Quorum

\* If the intersection of two server sets is empty, then they can't both be quorums.
LEMMA EmptyIntersectionImpliesNotBothQuorums == 
    \A s1 \in SUBSET Server :
    \A s2 \in SUBSET Server :
        (s1 \cap s2 = {}) => ~(s1 \in Quorum /\ s2 \in Quorum)


LEMMA StaticQuorumsOverlap == \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}


\* Proof Graph Stats
\* ==================
\* seed: None
\* num proof graph nodes: 39
\* num proof obligations: 429

IndGlobal == 
  /\ TypeOK
  /\ H_NoLogDivergence
  /\ H_CommitIndexInAppendEntriesImpliesCommittedEntryExists
  /\ H_LogMatching
  /\ H_LeaderMatchIndexValid
  /\ H_CommitIndexCoveredOnQuorum
  /\ H_CommitIndexBoundValid
  /\ H_PrimaryHasEntriesItCreated
  /\ H_LogMatchingAppendEntries
  /\ H_LeaderMatchIndexBound
  /\ H_LeaderMatchIndexValidAppendEntries
  /\ H_OnePrimaryPerTerm
  /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm
  /\ H_PrimaryHasEntriesItCreatedAppendEntries
  /\ H_LogMatchingInAppendEntriesMsgsLeaders
  /\ H_LogMatchingBetweenAppendEntriesMsgs
  /\ H_AppendEntriesRequestLogEntriesMustBeInLeaderLog
  /\ H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm
  /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLeader
  /\ H_LogEntryInTermImpliesSafeAtTerm
  /\ H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm
  /\ H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm
  /\ H_LogEntryInTermImpliesSafeAtTermAppendEntries
  /\ H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm
  /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm
  /\ H_LeaderHasVotesGrantedQuorum
  /\ H_VoteGrantedImpliesVoteResponseMsgConsistent
  /\ H_VoteInGrantedImpliesVotedFor
  /\ H_VoteGrantedImpliesNodeSafeAtTerm
  /\ H_CandidateInTermVotedForItself
  /\ H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm
  /\ H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm
  /\ H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm
  /\ H_AppendEntriesRequestInTermImpliesSafeAtTerms
  /\ H_AppendEntriesResponseInTermImpliesSafeAtTerms
  /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm
  /\ H_RequestVoteResponseTermsMatchSource
  /\ H_RequestVoteResponseMsgsInTermUnique
  /\ H_QuorumsSafeAtTerms
  /\ H_RequestVoteRequestFromNodeImpliesSafeAtTerm


\* mean in-degree: 2.4615384615384617
\* median in-degree: 2
\* max in-degree: 7
\* min in-degree: 0
\* mean variable slice size: 0

ASSUME A0 == IsFiniteSet(Server) /\ Cardinality(Server) > 1
ASSUME A1 == Nil \notin Server
ASSUME A2 == (Leader # Follower) /\ (Leader # Candidate)
ASSUME A3 == (Follower # Candidate)
ASSUME A4 == Server = Server
ASSUME A5 == Quorum \subseteq SUBSET Server /\ {} \notin Quorum /\ Quorum # {} /\ \A s \in Server : {s} \notin Quorum
ASSUME A6 == MaxLogLen \in Nat
ASSUME A7 == MaxTerm \in Nat

\*** H_RequestVoteRequestFromNodeImpliesSafeAtTerm
THEOREM L_0 == TypeOK /\ H_RequestVoteRequestFromNodeImpliesSafeAtTerm /\ Next => H_RequestVoteRequestFromNodeImpliesSafeAtTerm'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_RequestVoteRequestFromNodeImpliesSafeAtTerm,RequestVoteAction)
  <1>1. TypeOK /\ H_RequestVoteRequestFromNodeImpliesSafeAtTerm /\ RequestVoteAction => H_RequestVoteRequestFromNodeImpliesSafeAtTerm' BY DEF TypeOK,RequestVoteAction,RequestVote,H_RequestVoteRequestFromNodeImpliesSafeAtTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_RequestVoteRequestFromNodeImpliesSafeAtTerm,UpdateTermAction)
  <1>2. TypeOK /\ H_RequestVoteRequestFromNodeImpliesSafeAtTerm /\ UpdateTermAction => H_RequestVoteRequestFromNodeImpliesSafeAtTerm' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_RequestVoteRequestFromNodeImpliesSafeAtTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_RequestVoteRequestFromNodeImpliesSafeAtTerm,BecomeLeaderAction)
  <1>3. TypeOK /\ H_RequestVoteRequestFromNodeImpliesSafeAtTerm /\ BecomeLeaderAction => H_RequestVoteRequestFromNodeImpliesSafeAtTerm' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_RequestVoteRequestFromNodeImpliesSafeAtTerm
  \* (H_RequestVoteRequestFromNodeImpliesSafeAtTerm,ClientRequestAction)
  <1>4. TypeOK /\ H_RequestVoteRequestFromNodeImpliesSafeAtTerm /\ ClientRequestAction => H_RequestVoteRequestFromNodeImpliesSafeAtTerm' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_RequestVoteRequestFromNodeImpliesSafeAtTerm
  \* (H_RequestVoteRequestFromNodeImpliesSafeAtTerm,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_RequestVoteRequestFromNodeImpliesSafeAtTerm /\ AdvanceCommitIndexAction => H_RequestVoteRequestFromNodeImpliesSafeAtTerm' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_RequestVoteRequestFromNodeImpliesSafeAtTerm
  \* (H_RequestVoteRequestFromNodeImpliesSafeAtTerm,AppendEntriesAction)
  <1>6. TypeOK /\ H_RequestVoteRequestFromNodeImpliesSafeAtTerm /\ AppendEntriesAction => H_RequestVoteRequestFromNodeImpliesSafeAtTerm' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_RequestVoteRequestFromNodeImpliesSafeAtTerm
  \* (H_RequestVoteRequestFromNodeImpliesSafeAtTerm,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_RequestVoteRequestFromNodeImpliesSafeAtTerm /\ HandleRequestVoteRequestAction => H_RequestVoteRequestFromNodeImpliesSafeAtTerm' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_RequestVoteRequestFromNodeImpliesSafeAtTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_RequestVoteRequestFromNodeImpliesSafeAtTerm,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_RequestVoteRequestFromNodeImpliesSafeAtTerm /\ HandleRequestVoteResponseAction => H_RequestVoteRequestFromNodeImpliesSafeAtTerm' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_RequestVoteRequestFromNodeImpliesSafeAtTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_RequestVoteRequestFromNodeImpliesSafeAtTerm,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_RequestVoteRequestFromNodeImpliesSafeAtTerm /\ AcceptAppendEntriesRequestAppendAction => H_RequestVoteRequestFromNodeImpliesSafeAtTerm' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_RequestVoteRequestFromNodeImpliesSafeAtTerm
  \* (H_RequestVoteRequestFromNodeImpliesSafeAtTerm,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_RequestVoteRequestFromNodeImpliesSafeAtTerm /\ AcceptAppendEntriesRequestLearnCommitAction => H_RequestVoteRequestFromNodeImpliesSafeAtTerm' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_RequestVoteRequestFromNodeImpliesSafeAtTerm
  \* (H_RequestVoteRequestFromNodeImpliesSafeAtTerm,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_RequestVoteRequestFromNodeImpliesSafeAtTerm /\ HandleAppendEntriesResponseAction => H_RequestVoteRequestFromNodeImpliesSafeAtTerm' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_RequestVoteRequestFromNodeImpliesSafeAtTerm
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_QuorumsSafeAtTerms
THEOREM L_1 == TypeOK /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm /\ H_CandidateInTermVotedForItself /\ H_VoteInGrantedImpliesVotedFor /\ H_QuorumsSafeAtTerms /\ Next => H_QuorumsSafeAtTerms'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_QuorumsSafeAtTerms,RequestVoteAction)
  <1>1. TypeOK /\ H_QuorumsSafeAtTerms /\ RequestVoteAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,RequestVoteAction,RequestVote,H_QuorumsSafeAtTerms,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_QuorumsSafeAtTerms,UpdateTermAction)
  <1>2. TypeOK /\ H_QuorumsSafeAtTerms /\ UpdateTermAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_QuorumsSafeAtTerms,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_QuorumsSafeAtTerms,BecomeLeaderAction)
  <1>3. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm /\ H_CandidateInTermVotedForItself /\ H_VoteInGrantedImpliesVotedFor /\ H_QuorumsSafeAtTerms /\ BecomeLeaderAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm,H_CandidateInTermVotedForItself,H_VoteInGrantedImpliesVotedFor,BecomeLeaderAction,BecomeLeader,H_QuorumsSafeAtTerms
  \* (H_QuorumsSafeAtTerms,ClientRequestAction)
  <1>4. TypeOK /\ H_QuorumsSafeAtTerms /\ ClientRequestAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_QuorumsSafeAtTerms
  \* (H_QuorumsSafeAtTerms,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_QuorumsSafeAtTerms /\ AdvanceCommitIndexAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_QuorumsSafeAtTerms
  \* (H_QuorumsSafeAtTerms,AppendEntriesAction)
  <1>6. TypeOK /\ H_QuorumsSafeAtTerms /\ AppendEntriesAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_QuorumsSafeAtTerms
  \* (H_QuorumsSafeAtTerms,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_QuorumsSafeAtTerms /\ HandleRequestVoteRequestAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_QuorumsSafeAtTerms,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_QuorumsSafeAtTerms,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_QuorumsSafeAtTerms /\ HandleRequestVoteResponseAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_QuorumsSafeAtTerms,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_QuorumsSafeAtTerms,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_QuorumsSafeAtTerms /\ AcceptAppendEntriesRequestAppendAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_QuorumsSafeAtTerms
  \* (H_QuorumsSafeAtTerms,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_QuorumsSafeAtTerms /\ AcceptAppendEntriesRequestLearnCommitAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_QuorumsSafeAtTerms
  \* (H_QuorumsSafeAtTerms,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_QuorumsSafeAtTerms /\ HandleAppendEntriesResponseAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_QuorumsSafeAtTerms
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_RequestVoteResponseMsgsInTermUnique
THEOREM L_2 == TypeOK /\ H_RequestVoteResponseTermsMatchSource /\ H_RequestVoteResponseMsgsInTermUnique /\ Next => H_RequestVoteResponseMsgsInTermUnique'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_RequestVoteResponseMsgsInTermUnique,RequestVoteAction)
  <1>1. TypeOK /\ H_RequestVoteResponseMsgsInTermUnique /\ RequestVoteAction => H_RequestVoteResponseMsgsInTermUnique' BY DEF TypeOK,RequestVoteAction,RequestVote,H_RequestVoteResponseMsgsInTermUnique,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_RequestVoteResponseMsgsInTermUnique,UpdateTermAction)
  <1>2. TypeOK /\ H_RequestVoteResponseMsgsInTermUnique /\ UpdateTermAction => H_RequestVoteResponseMsgsInTermUnique' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_RequestVoteResponseMsgsInTermUnique,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_RequestVoteResponseMsgsInTermUnique,BecomeLeaderAction)
  <1>3. TypeOK /\ H_RequestVoteResponseMsgsInTermUnique /\ BecomeLeaderAction => H_RequestVoteResponseMsgsInTermUnique' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_RequestVoteResponseMsgsInTermUnique
  \* (H_RequestVoteResponseMsgsInTermUnique,ClientRequestAction)
  <1>4. TypeOK /\ H_RequestVoteResponseMsgsInTermUnique /\ ClientRequestAction => H_RequestVoteResponseMsgsInTermUnique' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_RequestVoteResponseMsgsInTermUnique
  \* (H_RequestVoteResponseMsgsInTermUnique,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_RequestVoteResponseMsgsInTermUnique /\ AdvanceCommitIndexAction => H_RequestVoteResponseMsgsInTermUnique' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_RequestVoteResponseMsgsInTermUnique
  \* (H_RequestVoteResponseMsgsInTermUnique,AppendEntriesAction)
  <1>6. TypeOK /\ H_RequestVoteResponseMsgsInTermUnique /\ AppendEntriesAction => H_RequestVoteResponseMsgsInTermUnique' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_RequestVoteResponseMsgsInTermUnique
  \* (H_RequestVoteResponseMsgsInTermUnique,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_RequestVoteResponseTermsMatchSource /\ H_RequestVoteResponseMsgsInTermUnique /\ HandleRequestVoteRequestAction => H_RequestVoteResponseMsgsInTermUnique' BY DEF TypeOK,H_RequestVoteResponseTermsMatchSource,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_RequestVoteResponseMsgsInTermUnique,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_RequestVoteResponseMsgsInTermUnique,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_RequestVoteResponseMsgsInTermUnique /\ HandleRequestVoteResponseAction => H_RequestVoteResponseMsgsInTermUnique' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_RequestVoteResponseMsgsInTermUnique,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_RequestVoteResponseMsgsInTermUnique,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_RequestVoteResponseMsgsInTermUnique /\ AcceptAppendEntriesRequestAppendAction => H_RequestVoteResponseMsgsInTermUnique' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_RequestVoteResponseMsgsInTermUnique
  \* (H_RequestVoteResponseMsgsInTermUnique,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_RequestVoteResponseMsgsInTermUnique /\ AcceptAppendEntriesRequestLearnCommitAction => H_RequestVoteResponseMsgsInTermUnique' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_RequestVoteResponseMsgsInTermUnique
  \* (H_RequestVoteResponseMsgsInTermUnique,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_RequestVoteResponseMsgsInTermUnique /\ HandleAppendEntriesResponseAction => H_RequestVoteResponseMsgsInTermUnique' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_RequestVoteResponseMsgsInTermUnique
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_RequestVoteResponseTermsMatchSource
THEOREM L_3 == TypeOK /\ H_RequestVoteResponseTermsMatchSource /\ Next => H_RequestVoteResponseTermsMatchSource'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_RequestVoteResponseTermsMatchSource,RequestVoteAction)
  <1>1. TypeOK /\ H_RequestVoteResponseTermsMatchSource /\ RequestVoteAction => H_RequestVoteResponseTermsMatchSource' BY DEF TypeOK,RequestVoteAction,RequestVote,H_RequestVoteResponseTermsMatchSource,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_RequestVoteResponseTermsMatchSource,UpdateTermAction)
  <1>2. TypeOK /\ H_RequestVoteResponseTermsMatchSource /\ UpdateTermAction => H_RequestVoteResponseTermsMatchSource' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_RequestVoteResponseTermsMatchSource,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_RequestVoteResponseTermsMatchSource,BecomeLeaderAction)
  <1>3. TypeOK /\ H_RequestVoteResponseTermsMatchSource /\ BecomeLeaderAction => H_RequestVoteResponseTermsMatchSource' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_RequestVoteResponseTermsMatchSource
  \* (H_RequestVoteResponseTermsMatchSource,ClientRequestAction)
  <1>4. TypeOK /\ H_RequestVoteResponseTermsMatchSource /\ ClientRequestAction => H_RequestVoteResponseTermsMatchSource' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_RequestVoteResponseTermsMatchSource
  \* (H_RequestVoteResponseTermsMatchSource,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_RequestVoteResponseTermsMatchSource /\ AdvanceCommitIndexAction => H_RequestVoteResponseTermsMatchSource' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_RequestVoteResponseTermsMatchSource
  \* (H_RequestVoteResponseTermsMatchSource,AppendEntriesAction)
  <1>6. TypeOK /\ H_RequestVoteResponseTermsMatchSource /\ AppendEntriesAction => H_RequestVoteResponseTermsMatchSource' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_RequestVoteResponseTermsMatchSource
  \* (H_RequestVoteResponseTermsMatchSource,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_RequestVoteResponseTermsMatchSource /\ HandleRequestVoteRequestAction => H_RequestVoteResponseTermsMatchSource' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_RequestVoteResponseTermsMatchSource,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_RequestVoteResponseTermsMatchSource,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_RequestVoteResponseTermsMatchSource /\ HandleRequestVoteResponseAction => H_RequestVoteResponseTermsMatchSource' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_RequestVoteResponseTermsMatchSource,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_RequestVoteResponseTermsMatchSource,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_RequestVoteResponseTermsMatchSource /\ AcceptAppendEntriesRequestAppendAction => H_RequestVoteResponseTermsMatchSource' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_RequestVoteResponseTermsMatchSource
  \* (H_RequestVoteResponseTermsMatchSource,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_RequestVoteResponseTermsMatchSource /\ AcceptAppendEntriesRequestLearnCommitAction => H_RequestVoteResponseTermsMatchSource' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_RequestVoteResponseTermsMatchSource
  \* (H_RequestVoteResponseTermsMatchSource,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_RequestVoteResponseTermsMatchSource /\ HandleAppendEntriesResponseAction => H_RequestVoteResponseTermsMatchSource' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_RequestVoteResponseTermsMatchSource
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm
THEOREM L_4 == TypeOK /\ H_RequestVoteResponseTermsMatchSource /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm /\ Next => H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm,RequestVoteAction)
  <1>1. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm /\ RequestVoteAction => H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm' BY DEF TypeOK,RequestVoteAction,RequestVote,H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm,UpdateTermAction)
  <1>2. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm /\ UpdateTermAction => H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm,BecomeLeaderAction)
  <1>3. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm /\ BecomeLeaderAction => H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm
  \* (H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm,ClientRequestAction)
  <1>4. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm /\ ClientRequestAction => H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm
  \* (H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm /\ AdvanceCommitIndexAction => H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm
  \* (H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm,AppendEntriesAction)
  <1>6. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm /\ AppendEntriesAction => H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm
  \* (H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm /\ HandleRequestVoteRequestAction => H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_RequestVoteResponseTermsMatchSource /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm /\ HandleRequestVoteResponseAction => H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm' BY DEF TypeOK,H_RequestVoteResponseTermsMatchSource,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm /\ AcceptAppendEntriesRequestAppendAction => H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm
  \* (H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm /\ AcceptAppendEntriesRequestLearnCommitAction => H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm
  \* (H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm /\ HandleAppendEntriesResponseAction => H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_AppendEntriesResponseInTermImpliesSafeAtTerms
THEOREM L_5 == TypeOK /\ H_AppendEntriesRequestInTermImpliesSafeAtTerms /\ H_AppendEntriesResponseInTermImpliesSafeAtTerms /\ Next => H_AppendEntriesResponseInTermImpliesSafeAtTerms'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_AppendEntriesResponseInTermImpliesSafeAtTerms,RequestVoteAction)
  <1>1. TypeOK /\ H_AppendEntriesResponseInTermImpliesSafeAtTerms /\ RequestVoteAction => H_AppendEntriesResponseInTermImpliesSafeAtTerms' BY DEF TypeOK,RequestVoteAction,RequestVote,H_AppendEntriesResponseInTermImpliesSafeAtTerms,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_AppendEntriesResponseInTermImpliesSafeAtTerms,UpdateTermAction)
  <1>2. TypeOK /\ H_AppendEntriesResponseInTermImpliesSafeAtTerms /\ UpdateTermAction => H_AppendEntriesResponseInTermImpliesSafeAtTerms' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_AppendEntriesResponseInTermImpliesSafeAtTerms,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_AppendEntriesResponseInTermImpliesSafeAtTerms,BecomeLeaderAction)
  <1>3. TypeOK /\ H_AppendEntriesResponseInTermImpliesSafeAtTerms /\ BecomeLeaderAction => H_AppendEntriesResponseInTermImpliesSafeAtTerms' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_AppendEntriesResponseInTermImpliesSafeAtTerms
  \* (H_AppendEntriesResponseInTermImpliesSafeAtTerms,ClientRequestAction)
  <1>4. TypeOK /\ H_AppendEntriesResponseInTermImpliesSafeAtTerms /\ ClientRequestAction => H_AppendEntriesResponseInTermImpliesSafeAtTerms' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_AppendEntriesResponseInTermImpliesSafeAtTerms
  \* (H_AppendEntriesResponseInTermImpliesSafeAtTerms,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_AppendEntriesResponseInTermImpliesSafeAtTerms /\ AdvanceCommitIndexAction => H_AppendEntriesResponseInTermImpliesSafeAtTerms' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_AppendEntriesResponseInTermImpliesSafeAtTerms
  \* (H_AppendEntriesResponseInTermImpliesSafeAtTerms,AppendEntriesAction)
  <1>6. TypeOK /\ H_AppendEntriesResponseInTermImpliesSafeAtTerms /\ AppendEntriesAction => H_AppendEntriesResponseInTermImpliesSafeAtTerms' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_AppendEntriesResponseInTermImpliesSafeAtTerms
  \* (H_AppendEntriesResponseInTermImpliesSafeAtTerms,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_AppendEntriesResponseInTermImpliesSafeAtTerms /\ HandleRequestVoteRequestAction => H_AppendEntriesResponseInTermImpliesSafeAtTerms' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_AppendEntriesResponseInTermImpliesSafeAtTerms,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_AppendEntriesResponseInTermImpliesSafeAtTerms,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_AppendEntriesResponseInTermImpliesSafeAtTerms /\ HandleRequestVoteResponseAction => H_AppendEntriesResponseInTermImpliesSafeAtTerms' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_AppendEntriesResponseInTermImpliesSafeAtTerms,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_AppendEntriesResponseInTermImpliesSafeAtTerms,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_AppendEntriesRequestInTermImpliesSafeAtTerms /\ H_AppendEntriesResponseInTermImpliesSafeAtTerms /\ AcceptAppendEntriesRequestAppendAction => H_AppendEntriesResponseInTermImpliesSafeAtTerms' BY DEF TypeOK,H_AppendEntriesRequestInTermImpliesSafeAtTerms,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_AppendEntriesResponseInTermImpliesSafeAtTerms
  \* (H_AppendEntriesResponseInTermImpliesSafeAtTerms,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_AppendEntriesResponseInTermImpliesSafeAtTerms /\ AcceptAppendEntriesRequestLearnCommitAction => H_AppendEntriesResponseInTermImpliesSafeAtTerms' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_AppendEntriesResponseInTermImpliesSafeAtTerms
  \* (H_AppendEntriesResponseInTermImpliesSafeAtTerms,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_AppendEntriesResponseInTermImpliesSafeAtTerms /\ HandleAppendEntriesResponseAction => H_AppendEntriesResponseInTermImpliesSafeAtTerms' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_AppendEntriesResponseInTermImpliesSafeAtTerms
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_AppendEntriesRequestInTermImpliesSafeAtTerms
THEOREM L_6 == TypeOK /\ H_QuorumsSafeAtTerms /\ H_AppendEntriesRequestInTermImpliesSafeAtTerms /\ Next => H_AppendEntriesRequestInTermImpliesSafeAtTerms'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_AppendEntriesRequestInTermImpliesSafeAtTerms,RequestVoteAction)
  <1>1. TypeOK /\ H_AppendEntriesRequestInTermImpliesSafeAtTerms /\ RequestVoteAction => H_AppendEntriesRequestInTermImpliesSafeAtTerms' BY DEF TypeOK,RequestVoteAction,RequestVote,H_AppendEntriesRequestInTermImpliesSafeAtTerms,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_AppendEntriesRequestInTermImpliesSafeAtTerms,UpdateTermAction)
  <1>2. TypeOK /\ H_AppendEntriesRequestInTermImpliesSafeAtTerms /\ UpdateTermAction => H_AppendEntriesRequestInTermImpliesSafeAtTerms' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_AppendEntriesRequestInTermImpliesSafeAtTerms,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_AppendEntriesRequestInTermImpliesSafeAtTerms,BecomeLeaderAction)
  <1>3. TypeOK /\ H_AppendEntriesRequestInTermImpliesSafeAtTerms /\ BecomeLeaderAction => H_AppendEntriesRequestInTermImpliesSafeAtTerms' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_AppendEntriesRequestInTermImpliesSafeAtTerms
  \* (H_AppendEntriesRequestInTermImpliesSafeAtTerms,ClientRequestAction)
  <1>4. TypeOK /\ H_AppendEntriesRequestInTermImpliesSafeAtTerms /\ ClientRequestAction => H_AppendEntriesRequestInTermImpliesSafeAtTerms' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_AppendEntriesRequestInTermImpliesSafeAtTerms
  \* (H_AppendEntriesRequestInTermImpliesSafeAtTerms,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_AppendEntriesRequestInTermImpliesSafeAtTerms /\ AdvanceCommitIndexAction => H_AppendEntriesRequestInTermImpliesSafeAtTerms' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_AppendEntriesRequestInTermImpliesSafeAtTerms
  \* (H_AppendEntriesRequestInTermImpliesSafeAtTerms,AppendEntriesAction)
  <1>6. TypeOK /\ H_QuorumsSafeAtTerms /\ H_AppendEntriesRequestInTermImpliesSafeAtTerms /\ AppendEntriesAction => H_AppendEntriesRequestInTermImpliesSafeAtTerms' BY DEF TypeOK,H_QuorumsSafeAtTerms,AppendEntriesAction,AppendEntries,H_AppendEntriesRequestInTermImpliesSafeAtTerms
  \* (H_AppendEntriesRequestInTermImpliesSafeAtTerms,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_AppendEntriesRequestInTermImpliesSafeAtTerms /\ HandleRequestVoteRequestAction => H_AppendEntriesRequestInTermImpliesSafeAtTerms' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_AppendEntriesRequestInTermImpliesSafeAtTerms,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_AppendEntriesRequestInTermImpliesSafeAtTerms,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_AppendEntriesRequestInTermImpliesSafeAtTerms /\ HandleRequestVoteResponseAction => H_AppendEntriesRequestInTermImpliesSafeAtTerms' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_AppendEntriesRequestInTermImpliesSafeAtTerms,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_AppendEntriesRequestInTermImpliesSafeAtTerms,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_AppendEntriesRequestInTermImpliesSafeAtTerms /\ AcceptAppendEntriesRequestAppendAction => H_AppendEntriesRequestInTermImpliesSafeAtTerms' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_AppendEntriesRequestInTermImpliesSafeAtTerms
  \* (H_AppendEntriesRequestInTermImpliesSafeAtTerms,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_AppendEntriesRequestInTermImpliesSafeAtTerms /\ AcceptAppendEntriesRequestLearnCommitAction => H_AppendEntriesRequestInTermImpliesSafeAtTerms' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_AppendEntriesRequestInTermImpliesSafeAtTerms
  \* (H_AppendEntriesRequestInTermImpliesSafeAtTerms,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_AppendEntriesRequestInTermImpliesSafeAtTerms /\ HandleAppendEntriesResponseAction => H_AppendEntriesRequestInTermImpliesSafeAtTerms' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_AppendEntriesRequestInTermImpliesSafeAtTerms
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm
THEOREM L_7 == TypeOK /\ H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm /\ H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm /\ H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ H_CandidateInTermVotedForItself /\ H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm /\ Next => H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm,RequestVoteAction)
  <1>1. TypeOK /\ H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm /\ H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm /\ RequestVoteAction => H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm' BY DEF TypeOK,H_LogEntryInTermImpliesSafeAtTermAppendEntries,H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm,RequestVoteAction,RequestVote,H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm,UpdateTermAction)
  <1>2. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm /\ UpdateTermAction => H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm,BecomeLeaderAction)
  <1>3. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm /\ BecomeLeaderAction => H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm
  \* (H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm,ClientRequestAction)
  <1>4. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm /\ ClientRequestAction => H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm
  \* (H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm /\ AdvanceCommitIndexAction => H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm
  \* (H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm,AppendEntriesAction)
  <1>6. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm /\ H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm /\ AppendEntriesAction => H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm' BY DEF TypeOK,H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,AppendEntriesAction,AppendEntries,H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm
  \* (H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ H_CandidateInTermVotedForItself /\ H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm /\ HandleRequestVoteRequestAction => H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm' BY DEF TypeOK,H_LogEntryInTermImpliesSafeAtTermAppendEntries,H_CandidateInTermVotedForItself,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm /\ HandleRequestVoteResponseAction => H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm /\ AcceptAppendEntriesRequestAppendAction => H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm
  \* (H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm /\ AcceptAppendEntriesRequestLearnCommitAction => H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm
  \* (H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm /\ HandleAppendEntriesResponseAction => H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm
THEOREM L_8 == TypeOK /\ H_RequestVoteRequestFromNodeImpliesSafeAtTerm /\ H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm /\ Next => H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm,RequestVoteAction)
  <1>1. TypeOK /\ H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm /\ RequestVoteAction => H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm' BY DEF TypeOK,RequestVoteAction,RequestVote,H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm,UpdateTermAction)
  <1>2. TypeOK /\ H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm /\ UpdateTermAction => H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm,BecomeLeaderAction)
  <1>3. TypeOK /\ H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm /\ BecomeLeaderAction => H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm
  \* (H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm,ClientRequestAction)
  <1>4. TypeOK /\ H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm /\ ClientRequestAction => H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm
  \* (H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm /\ AdvanceCommitIndexAction => H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm
  \* (H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm,AppendEntriesAction)
  <1>6. TypeOK /\ H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm /\ AppendEntriesAction => H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm
  \* (H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_RequestVoteRequestFromNodeImpliesSafeAtTerm /\ H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm /\ HandleRequestVoteRequestAction => H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm' BY DEF TypeOK,H_RequestVoteRequestFromNodeImpliesSafeAtTerm,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm /\ HandleRequestVoteResponseAction => H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm /\ AcceptAppendEntriesRequestAppendAction => H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm
  \* (H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm /\ AcceptAppendEntriesRequestLearnCommitAction => H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm
  \* (H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm /\ HandleAppendEntriesResponseAction => H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm
THEOREM L_9 == TypeOK /\ H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm /\ H_VoteGrantedImpliesVoteResponseMsgConsistent /\ H_CandidateInTermVotedForItself /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ H_QuorumsSafeAtTerms /\ H_CandidateInTermVotedForItself /\ H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm /\ Next => H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm,RequestVoteAction)
  <1>1. TypeOK /\ H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm /\ H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm /\ RequestVoteAction => H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm' BY DEF TypeOK,H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm,RequestVoteAction,RequestVote,H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm,UpdateTermAction)
  <1>2. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm /\ UpdateTermAction => H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm,BecomeLeaderAction)
  <1>3. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm /\ H_VoteGrantedImpliesVoteResponseMsgConsistent /\ H_CandidateInTermVotedForItself /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm /\ BecomeLeaderAction => H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm' BY DEF TypeOK,H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm,H_VoteGrantedImpliesVoteResponseMsgConsistent,H_CandidateInTermVotedForItself,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,BecomeLeaderAction,BecomeLeader,H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm
  \* (H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm,ClientRequestAction)
  <1>4. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm /\ ClientRequestAction => H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm
  \* (H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm /\ AdvanceCommitIndexAction => H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm
  \* (H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm,AppendEntriesAction)
  <1>6. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm /\ AppendEntriesAction => H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm
  \* (H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_QuorumsSafeAtTerms /\ H_CandidateInTermVotedForItself /\ H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm /\ HandleRequestVoteRequestAction => H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm' BY DEF TypeOK,H_QuorumsSafeAtTerms,H_CandidateInTermVotedForItself,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm /\ HandleRequestVoteResponseAction => H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm /\ AcceptAppendEntriesRequestAppendAction => H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm
  \* (H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm /\ AcceptAppendEntriesRequestLearnCommitAction => H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm
  \* (H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm /\ HandleAppendEntriesResponseAction => H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_CandidateInTermVotedForItself
THEOREM L_10 == TypeOK /\ H_CandidateInTermVotedForItself /\ Next => H_CandidateInTermVotedForItself'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_CandidateInTermVotedForItself,RequestVoteAction)
  <1>1. TypeOK /\ H_CandidateInTermVotedForItself /\ RequestVoteAction => H_CandidateInTermVotedForItself' BY DEF TypeOK,RequestVoteAction,RequestVote,H_CandidateInTermVotedForItself,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_CandidateInTermVotedForItself,UpdateTermAction)
  <1>2. TypeOK /\ H_CandidateInTermVotedForItself /\ UpdateTermAction => H_CandidateInTermVotedForItself' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_CandidateInTermVotedForItself,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_CandidateInTermVotedForItself,BecomeLeaderAction)
  <1>3. TypeOK /\ H_CandidateInTermVotedForItself /\ BecomeLeaderAction => H_CandidateInTermVotedForItself' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_CandidateInTermVotedForItself
  \* (H_CandidateInTermVotedForItself,ClientRequestAction)
  <1>4. TypeOK /\ H_CandidateInTermVotedForItself /\ ClientRequestAction => H_CandidateInTermVotedForItself' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_CandidateInTermVotedForItself
  \* (H_CandidateInTermVotedForItself,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_CandidateInTermVotedForItself /\ AdvanceCommitIndexAction => H_CandidateInTermVotedForItself' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_CandidateInTermVotedForItself
  \* (H_CandidateInTermVotedForItself,AppendEntriesAction)
  <1>6. TypeOK /\ H_CandidateInTermVotedForItself /\ AppendEntriesAction => H_CandidateInTermVotedForItself' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_CandidateInTermVotedForItself
  \* (H_CandidateInTermVotedForItself,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_CandidateInTermVotedForItself /\ HandleRequestVoteRequestAction => H_CandidateInTermVotedForItself' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_CandidateInTermVotedForItself,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_CandidateInTermVotedForItself,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_CandidateInTermVotedForItself /\ HandleRequestVoteResponseAction => H_CandidateInTermVotedForItself' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_CandidateInTermVotedForItself,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_CandidateInTermVotedForItself,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_CandidateInTermVotedForItself /\ AcceptAppendEntriesRequestAppendAction => H_CandidateInTermVotedForItself' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_CandidateInTermVotedForItself
  \* (H_CandidateInTermVotedForItself,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_CandidateInTermVotedForItself /\ AcceptAppendEntriesRequestLearnCommitAction => H_CandidateInTermVotedForItself' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_CandidateInTermVotedForItself
  \* (H_CandidateInTermVotedForItself,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_CandidateInTermVotedForItself /\ HandleAppendEntriesResponseAction => H_CandidateInTermVotedForItself' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_CandidateInTermVotedForItself
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_VoteGrantedImpliesNodeSafeAtTerm
THEOREM L_11 == TypeOK /\ H_RequestVoteResponseTermsMatchSource /\ H_VoteGrantedImpliesNodeSafeAtTerm /\ Next => H_VoteGrantedImpliesNodeSafeAtTerm'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_VoteGrantedImpliesNodeSafeAtTerm,RequestVoteAction)
  <1>1. TypeOK /\ H_VoteGrantedImpliesNodeSafeAtTerm /\ RequestVoteAction => H_VoteGrantedImpliesNodeSafeAtTerm' BY DEF TypeOK,RequestVoteAction,RequestVote,H_VoteGrantedImpliesNodeSafeAtTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_VoteGrantedImpliesNodeSafeAtTerm,UpdateTermAction)
  <1>2. TypeOK /\ H_VoteGrantedImpliesNodeSafeAtTerm /\ UpdateTermAction => H_VoteGrantedImpliesNodeSafeAtTerm' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_VoteGrantedImpliesNodeSafeAtTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_VoteGrantedImpliesNodeSafeAtTerm,BecomeLeaderAction)
  <1>3. TypeOK /\ H_VoteGrantedImpliesNodeSafeAtTerm /\ BecomeLeaderAction => H_VoteGrantedImpliesNodeSafeAtTerm' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_VoteGrantedImpliesNodeSafeAtTerm
  \* (H_VoteGrantedImpliesNodeSafeAtTerm,ClientRequestAction)
  <1>4. TypeOK /\ H_VoteGrantedImpliesNodeSafeAtTerm /\ ClientRequestAction => H_VoteGrantedImpliesNodeSafeAtTerm' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_VoteGrantedImpliesNodeSafeAtTerm
  \* (H_VoteGrantedImpliesNodeSafeAtTerm,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_VoteGrantedImpliesNodeSafeAtTerm /\ AdvanceCommitIndexAction => H_VoteGrantedImpliesNodeSafeAtTerm' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_VoteGrantedImpliesNodeSafeAtTerm
  \* (H_VoteGrantedImpliesNodeSafeAtTerm,AppendEntriesAction)
  <1>6. TypeOK /\ H_VoteGrantedImpliesNodeSafeAtTerm /\ AppendEntriesAction => H_VoteGrantedImpliesNodeSafeAtTerm' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_VoteGrantedImpliesNodeSafeAtTerm
  \* (H_VoteGrantedImpliesNodeSafeAtTerm,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_VoteGrantedImpliesNodeSafeAtTerm /\ HandleRequestVoteRequestAction => H_VoteGrantedImpliesNodeSafeAtTerm' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_VoteGrantedImpliesNodeSafeAtTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_VoteGrantedImpliesNodeSafeAtTerm,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_RequestVoteResponseTermsMatchSource /\ H_VoteGrantedImpliesNodeSafeAtTerm /\ HandleRequestVoteResponseAction => H_VoteGrantedImpliesNodeSafeAtTerm' BY DEF TypeOK,H_RequestVoteResponseTermsMatchSource,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_VoteGrantedImpliesNodeSafeAtTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_VoteGrantedImpliesNodeSafeAtTerm,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_VoteGrantedImpliesNodeSafeAtTerm /\ AcceptAppendEntriesRequestAppendAction => H_VoteGrantedImpliesNodeSafeAtTerm' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_VoteGrantedImpliesNodeSafeAtTerm
  \* (H_VoteGrantedImpliesNodeSafeAtTerm,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_VoteGrantedImpliesNodeSafeAtTerm /\ AcceptAppendEntriesRequestLearnCommitAction => H_VoteGrantedImpliesNodeSafeAtTerm' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_VoteGrantedImpliesNodeSafeAtTerm
  \* (H_VoteGrantedImpliesNodeSafeAtTerm,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_VoteGrantedImpliesNodeSafeAtTerm /\ HandleAppendEntriesResponseAction => H_VoteGrantedImpliesNodeSafeAtTerm' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_VoteGrantedImpliesNodeSafeAtTerm
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_VoteInGrantedImpliesVotedFor
THEOREM L_12 == TypeOK /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm /\ H_RequestVoteResponseTermsMatchSource /\ H_VoteInGrantedImpliesVotedFor /\ Next => H_VoteInGrantedImpliesVotedFor'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_VoteInGrantedImpliesVotedFor,RequestVoteAction)
  <1>1. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm /\ H_VoteInGrantedImpliesVotedFor /\ RequestVoteAction => H_VoteInGrantedImpliesVotedFor' BY DEF TypeOK,H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm,RequestVoteAction,RequestVote,H_VoteInGrantedImpliesVotedFor,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_VoteInGrantedImpliesVotedFor,UpdateTermAction)
  <1>2. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm /\ H_VoteInGrantedImpliesVotedFor /\ UpdateTermAction => H_VoteInGrantedImpliesVotedFor' BY DEF TypeOK,H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm,UpdateTermAction,UpdateTerm,H_VoteInGrantedImpliesVotedFor,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_VoteInGrantedImpliesVotedFor,BecomeLeaderAction)
  <1>3. TypeOK /\ H_VoteInGrantedImpliesVotedFor /\ BecomeLeaderAction => H_VoteInGrantedImpliesVotedFor' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_VoteInGrantedImpliesVotedFor
  \* (H_VoteInGrantedImpliesVotedFor,ClientRequestAction)
  <1>4. TypeOK /\ H_VoteInGrantedImpliesVotedFor /\ ClientRequestAction => H_VoteInGrantedImpliesVotedFor' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_VoteInGrantedImpliesVotedFor
  \* (H_VoteInGrantedImpliesVotedFor,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_VoteInGrantedImpliesVotedFor /\ AdvanceCommitIndexAction => H_VoteInGrantedImpliesVotedFor' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_VoteInGrantedImpliesVotedFor
  \* (H_VoteInGrantedImpliesVotedFor,AppendEntriesAction)
  <1>6. TypeOK /\ H_VoteInGrantedImpliesVotedFor /\ AppendEntriesAction => H_VoteInGrantedImpliesVotedFor' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_VoteInGrantedImpliesVotedFor
  \* (H_VoteInGrantedImpliesVotedFor,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_VoteInGrantedImpliesVotedFor /\ HandleRequestVoteRequestAction => H_VoteInGrantedImpliesVotedFor' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_VoteInGrantedImpliesVotedFor,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_VoteInGrantedImpliesVotedFor,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_RequestVoteResponseTermsMatchSource /\ H_VoteInGrantedImpliesVotedFor /\ HandleRequestVoteResponseAction => H_VoteInGrantedImpliesVotedFor' BY DEF TypeOK,H_RequestVoteResponseTermsMatchSource,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_VoteInGrantedImpliesVotedFor,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_VoteInGrantedImpliesVotedFor,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_VoteInGrantedImpliesVotedFor /\ AcceptAppendEntriesRequestAppendAction => H_VoteInGrantedImpliesVotedFor' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_VoteInGrantedImpliesVotedFor
  \* (H_VoteInGrantedImpliesVotedFor,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_VoteInGrantedImpliesVotedFor /\ AcceptAppendEntriesRequestLearnCommitAction => H_VoteInGrantedImpliesVotedFor' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_VoteInGrantedImpliesVotedFor
  \* (H_VoteInGrantedImpliesVotedFor,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_VoteInGrantedImpliesVotedFor /\ HandleAppendEntriesResponseAction => H_VoteInGrantedImpliesVotedFor' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_VoteInGrantedImpliesVotedFor
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_VoteGrantedImpliesVoteResponseMsgConsistent
THEOREM L_13 == TypeOK /\ H_RequestVoteResponseTermsMatchSource /\ H_VoteInGrantedImpliesVotedFor /\ H_VoteGrantedImpliesNodeSafeAtTerm /\ H_RequestVoteResponseMsgsInTermUnique /\ H_VoteGrantedImpliesNodeSafeAtTerm /\ H_VoteGrantedImpliesVoteResponseMsgConsistent /\ Next => H_VoteGrantedImpliesVoteResponseMsgConsistent'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_VoteGrantedImpliesVoteResponseMsgConsistent,RequestVoteAction)
  <1>1. TypeOK /\ H_RequestVoteResponseTermsMatchSource /\ H_VoteGrantedImpliesVoteResponseMsgConsistent /\ RequestVoteAction => H_VoteGrantedImpliesVoteResponseMsgConsistent' BY DEF TypeOK,H_RequestVoteResponseTermsMatchSource,RequestVoteAction,RequestVote,H_VoteGrantedImpliesVoteResponseMsgConsistent,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_VoteGrantedImpliesVoteResponseMsgConsistent,UpdateTermAction)
  <1>2. TypeOK /\ H_VoteGrantedImpliesVoteResponseMsgConsistent /\ UpdateTermAction => H_VoteGrantedImpliesVoteResponseMsgConsistent' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_VoteGrantedImpliesVoteResponseMsgConsistent,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_VoteGrantedImpliesVoteResponseMsgConsistent,BecomeLeaderAction)
  <1>3. TypeOK /\ H_VoteGrantedImpliesVoteResponseMsgConsistent /\ BecomeLeaderAction => H_VoteGrantedImpliesVoteResponseMsgConsistent' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_VoteGrantedImpliesVoteResponseMsgConsistent
  \* (H_VoteGrantedImpliesVoteResponseMsgConsistent,ClientRequestAction)
  <1>4. TypeOK /\ H_VoteGrantedImpliesVoteResponseMsgConsistent /\ ClientRequestAction => H_VoteGrantedImpliesVoteResponseMsgConsistent' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_VoteGrantedImpliesVoteResponseMsgConsistent
  \* (H_VoteGrantedImpliesVoteResponseMsgConsistent,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_VoteGrantedImpliesVoteResponseMsgConsistent /\ AdvanceCommitIndexAction => H_VoteGrantedImpliesVoteResponseMsgConsistent' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_VoteGrantedImpliesVoteResponseMsgConsistent
  \* (H_VoteGrantedImpliesVoteResponseMsgConsistent,AppendEntriesAction)
  <1>6. TypeOK /\ H_VoteGrantedImpliesVoteResponseMsgConsistent /\ AppendEntriesAction => H_VoteGrantedImpliesVoteResponseMsgConsistent' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_VoteGrantedImpliesVoteResponseMsgConsistent
  \* (H_VoteGrantedImpliesVoteResponseMsgConsistent,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_VoteInGrantedImpliesVotedFor /\ H_VoteGrantedImpliesNodeSafeAtTerm /\ H_VoteGrantedImpliesVoteResponseMsgConsistent /\ HandleRequestVoteRequestAction => H_VoteGrantedImpliesVoteResponseMsgConsistent' BY DEF TypeOK,H_VoteInGrantedImpliesVotedFor,H_VoteGrantedImpliesNodeSafeAtTerm,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_VoteGrantedImpliesVoteResponseMsgConsistent,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_VoteGrantedImpliesVoteResponseMsgConsistent,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_RequestVoteResponseMsgsInTermUnique /\ H_VoteGrantedImpliesNodeSafeAtTerm /\ H_VoteGrantedImpliesVoteResponseMsgConsistent /\ HandleRequestVoteResponseAction => H_VoteGrantedImpliesVoteResponseMsgConsistent' BY DEF TypeOK,H_RequestVoteResponseMsgsInTermUnique,H_VoteGrantedImpliesNodeSafeAtTerm,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_VoteGrantedImpliesVoteResponseMsgConsistent,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_VoteGrantedImpliesVoteResponseMsgConsistent,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_VoteGrantedImpliesVoteResponseMsgConsistent /\ AcceptAppendEntriesRequestAppendAction => H_VoteGrantedImpliesVoteResponseMsgConsistent' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_VoteGrantedImpliesVoteResponseMsgConsistent
  \* (H_VoteGrantedImpliesVoteResponseMsgConsistent,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_VoteGrantedImpliesVoteResponseMsgConsistent /\ AcceptAppendEntriesRequestLearnCommitAction => H_VoteGrantedImpliesVoteResponseMsgConsistent' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_VoteGrantedImpliesVoteResponseMsgConsistent
  \* (H_VoteGrantedImpliesVoteResponseMsgConsistent,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_VoteGrantedImpliesVoteResponseMsgConsistent /\ HandleAppendEntriesResponseAction => H_VoteGrantedImpliesVoteResponseMsgConsistent' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_VoteGrantedImpliesVoteResponseMsgConsistent
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_LeaderHasVotesGrantedQuorum
THEOREM L_14 == TypeOK /\ H_LeaderHasVotesGrantedQuorum /\ Next => H_LeaderHasVotesGrantedQuorum'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_LeaderHasVotesGrantedQuorum,RequestVoteAction)
  <1>1. TypeOK /\ H_LeaderHasVotesGrantedQuorum /\ RequestVoteAction => H_LeaderHasVotesGrantedQuorum' BY DEF TypeOK,RequestVoteAction,RequestVote,H_LeaderHasVotesGrantedQuorum,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_LeaderHasVotesGrantedQuorum,UpdateTermAction)
  <1>2. TypeOK /\ H_LeaderHasVotesGrantedQuorum /\ UpdateTermAction => H_LeaderHasVotesGrantedQuorum' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_LeaderHasVotesGrantedQuorum,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_LeaderHasVotesGrantedQuorum,BecomeLeaderAction)
  <1>3. TypeOK /\ H_LeaderHasVotesGrantedQuorum /\ BecomeLeaderAction => H_LeaderHasVotesGrantedQuorum' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_LeaderHasVotesGrantedQuorum
  \* (H_LeaderHasVotesGrantedQuorum,ClientRequestAction)
  <1>4. TypeOK /\ H_LeaderHasVotesGrantedQuorum /\ ClientRequestAction => H_LeaderHasVotesGrantedQuorum' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_LeaderHasVotesGrantedQuorum
  \* (H_LeaderHasVotesGrantedQuorum,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_LeaderHasVotesGrantedQuorum /\ AdvanceCommitIndexAction => H_LeaderHasVotesGrantedQuorum' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_LeaderHasVotesGrantedQuorum
  \* (H_LeaderHasVotesGrantedQuorum,AppendEntriesAction)
  <1>6. TypeOK /\ H_LeaderHasVotesGrantedQuorum /\ AppendEntriesAction => H_LeaderHasVotesGrantedQuorum' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_LeaderHasVotesGrantedQuorum
  \* (H_LeaderHasVotesGrantedQuorum,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_LeaderHasVotesGrantedQuorum /\ HandleRequestVoteRequestAction => H_LeaderHasVotesGrantedQuorum' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_LeaderHasVotesGrantedQuorum,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_LeaderHasVotesGrantedQuorum,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_LeaderHasVotesGrantedQuorum /\ HandleRequestVoteResponseAction => H_LeaderHasVotesGrantedQuorum' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_LeaderHasVotesGrantedQuorum,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_LeaderHasVotesGrantedQuorum,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_LeaderHasVotesGrantedQuorum /\ AcceptAppendEntriesRequestAppendAction => H_LeaderHasVotesGrantedQuorum' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_LeaderHasVotesGrantedQuorum
  \* (H_LeaderHasVotesGrantedQuorum,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_LeaderHasVotesGrantedQuorum /\ AcceptAppendEntriesRequestLearnCommitAction => H_LeaderHasVotesGrantedQuorum' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_LeaderHasVotesGrantedQuorum
  \* (H_LeaderHasVotesGrantedQuorum,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_LeaderHasVotesGrantedQuorum /\ HandleAppendEntriesResponseAction => H_LeaderHasVotesGrantedQuorum' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_LeaderHasVotesGrantedQuorum
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_VotesCantBeGrantedTwiceToCandidatesInSameTerm
THEOREM L_15 == TypeOK /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm /\ H_VoteGrantedImpliesNodeSafeAtTerm /\ H_VoteGrantedImpliesVoteResponseMsgConsistent /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ Next => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,RequestVoteAction)
  <1>1. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm /\ H_VoteGrantedImpliesNodeSafeAtTerm /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ RequestVoteAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm,H_VoteGrantedImpliesNodeSafeAtTerm,RequestVoteAction,RequestVote,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,UpdateTermAction)
  <1>2. TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ UpdateTermAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,BecomeLeaderAction)
  <1>3. TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ BecomeLeaderAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,ClientRequestAction)
  <1>4. TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ ClientRequestAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ AdvanceCommitIndexAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,AppendEntriesAction)
  <1>6. TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ AppendEntriesAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ HandleRequestVoteRequestAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_VoteGrantedImpliesVoteResponseMsgConsistent /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ HandleRequestVoteResponseAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,H_VoteGrantedImpliesVoteResponseMsgConsistent,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ AcceptAppendEntriesRequestAppendAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ AcceptAppendEntriesRequestLearnCommitAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ HandleAppendEntriesResponseAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm
THEOREM L_16 == TypeOK /\ H_AppendEntriesRequestInTermImpliesSafeAtTerms /\ H_AppendEntriesResponseInTermImpliesSafeAtTerms /\ H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm /\ H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm /\ H_AppendEntriesResponseInTermImpliesSafeAtTerms /\ H_AppendEntriesRequestInTermImpliesSafeAtTerms /\ H_CandidateInTermVotedForItself /\ H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm /\ Next => H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm,RequestVoteAction)
  <1>1. TypeOK /\ H_AppendEntriesRequestInTermImpliesSafeAtTerms /\ H_AppendEntriesResponseInTermImpliesSafeAtTerms /\ H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm /\ H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm /\ RequestVoteAction => H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm' BY DEF TypeOK,H_AppendEntriesRequestInTermImpliesSafeAtTerms,H_AppendEntriesResponseInTermImpliesSafeAtTerms,H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm,RequestVoteAction,RequestVote,H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm,UpdateTermAction)
  <1>2. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm /\ UpdateTermAction => H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm,BecomeLeaderAction)
  <1>3. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm /\ BecomeLeaderAction => H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm
  \* (H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm,ClientRequestAction)
  <1>4. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm /\ ClientRequestAction => H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm
  \* (H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm /\ AdvanceCommitIndexAction => H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm
  \* (H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm,AppendEntriesAction)
  <1>6. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm /\ H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm /\ AppendEntriesAction => H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm' BY DEF TypeOK,H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm,AppendEntriesAction,AppendEntries,H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm
  \* (H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_AppendEntriesResponseInTermImpliesSafeAtTerms /\ H_AppendEntriesRequestInTermImpliesSafeAtTerms /\ H_CandidateInTermVotedForItself /\ H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm /\ HandleRequestVoteRequestAction => H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm' BY DEF TypeOK,H_AppendEntriesResponseInTermImpliesSafeAtTerms,H_AppendEntriesRequestInTermImpliesSafeAtTerms,H_CandidateInTermVotedForItself,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm /\ HandleRequestVoteResponseAction => H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm /\ AcceptAppendEntriesRequestAppendAction => H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm
  \* (H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm /\ AcceptAppendEntriesRequestLearnCommitAction => H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm
  \* (H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm /\ HandleAppendEntriesResponseAction => H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_LogEntryInTermImpliesSafeAtTermAppendEntries
THEOREM L_17 == TypeOK /\ H_LogEntryInTermImpliesSafeAtTerm /\ H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ Next => H_LogEntryInTermImpliesSafeAtTermAppendEntries'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_LogEntryInTermImpliesSafeAtTermAppendEntries,RequestVoteAction)
  <1>1. TypeOK /\ H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ RequestVoteAction => H_LogEntryInTermImpliesSafeAtTermAppendEntries' BY DEF TypeOK,RequestVoteAction,RequestVote,H_LogEntryInTermImpliesSafeAtTermAppendEntries,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_LogEntryInTermImpliesSafeAtTermAppendEntries,UpdateTermAction)
  <1>2. TypeOK /\ H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ UpdateTermAction => H_LogEntryInTermImpliesSafeAtTermAppendEntries' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_LogEntryInTermImpliesSafeAtTermAppendEntries,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_LogEntryInTermImpliesSafeAtTermAppendEntries,BecomeLeaderAction)
  <1>3. TypeOK /\ H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ BecomeLeaderAction => H_LogEntryInTermImpliesSafeAtTermAppendEntries' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_LogEntryInTermImpliesSafeAtTermAppendEntries
  \* (H_LogEntryInTermImpliesSafeAtTermAppendEntries,ClientRequestAction)
  <1>4. TypeOK /\ H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ ClientRequestAction => H_LogEntryInTermImpliesSafeAtTermAppendEntries' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_LogEntryInTermImpliesSafeAtTermAppendEntries
  \* (H_LogEntryInTermImpliesSafeAtTermAppendEntries,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ AdvanceCommitIndexAction => H_LogEntryInTermImpliesSafeAtTermAppendEntries' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_LogEntryInTermImpliesSafeAtTermAppendEntries
  \* (H_LogEntryInTermImpliesSafeAtTermAppendEntries,AppendEntriesAction)
  <1>6. TypeOK /\ H_LogEntryInTermImpliesSafeAtTerm /\ H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ AppendEntriesAction => H_LogEntryInTermImpliesSafeAtTermAppendEntries' BY DEF TypeOK,H_LogEntryInTermImpliesSafeAtTerm,AppendEntriesAction,AppendEntries,H_LogEntryInTermImpliesSafeAtTermAppendEntries
  \* (H_LogEntryInTermImpliesSafeAtTermAppendEntries,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ HandleRequestVoteRequestAction => H_LogEntryInTermImpliesSafeAtTermAppendEntries' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_LogEntryInTermImpliesSafeAtTermAppendEntries,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_LogEntryInTermImpliesSafeAtTermAppendEntries,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ HandleRequestVoteResponseAction => H_LogEntryInTermImpliesSafeAtTermAppendEntries' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_LogEntryInTermImpliesSafeAtTermAppendEntries,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_LogEntryInTermImpliesSafeAtTermAppendEntries,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ AcceptAppendEntriesRequestAppendAction => H_LogEntryInTermImpliesSafeAtTermAppendEntries' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_LogEntryInTermImpliesSafeAtTermAppendEntries
  \* (H_LogEntryInTermImpliesSafeAtTermAppendEntries,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ AcceptAppendEntriesRequestLearnCommitAction => H_LogEntryInTermImpliesSafeAtTermAppendEntries' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_LogEntryInTermImpliesSafeAtTermAppendEntries
  \* (H_LogEntryInTermImpliesSafeAtTermAppendEntries,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ HandleAppendEntriesResponseAction => H_LogEntryInTermImpliesSafeAtTermAppendEntries' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_LogEntryInTermImpliesSafeAtTermAppendEntries
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm
THEOREM L_18 == TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm /\ H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm /\ H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm /\ Next => H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm,RequestVoteAction)
  <1>1. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm /\ RequestVoteAction => H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm' BY DEF TypeOK,RequestVoteAction,RequestVote,H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm,UpdateTermAction)
  <1>2. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm /\ UpdateTermAction => H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm,BecomeLeaderAction)
  <1>3. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm /\ BecomeLeaderAction => H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm
  \* (H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm,ClientRequestAction)
  <1>4. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm /\ ClientRequestAction => H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm
  \* (H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm /\ AdvanceCommitIndexAction => H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm
  \* (H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm,AppendEntriesAction)
  <1>6. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm /\ H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm /\ AppendEntriesAction => H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm' BY DEF TypeOK,H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm,AppendEntriesAction,AppendEntries,H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm
  \* (H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm /\ HandleRequestVoteRequestAction => H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm /\ H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm /\ HandleRequestVoteResponseAction => H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm' BY DEF TypeOK,H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm /\ AcceptAppendEntriesRequestAppendAction => H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm
  \* (H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm /\ AcceptAppendEntriesRequestLearnCommitAction => H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm
  \* (H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm /\ HandleAppendEntriesResponseAction => H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm
THEOREM L_19 == TypeOK /\ H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm /\ H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm /\ H_LogEntryInTermImpliesSafeAtTerm /\ H_CandidateInTermVotedForItself /\ H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm /\ H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm /\ Next => H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,RequestVoteAction)
  <1>1. TypeOK /\ H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm /\ H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm /\ RequestVoteAction => H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm' BY DEF TypeOK,H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm,RequestVoteAction,RequestVote,H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,ExistsRequestVoteResponseQuorum
  \* (H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,UpdateTermAction)
  <1>2. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm /\ UpdateTermAction => H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,ExistsRequestVoteResponseQuorum
  \* (H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,BecomeLeaderAction)
  <1>3. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm /\ BecomeLeaderAction => H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,ExistsRequestVoteResponseQuorum
  \* (H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,ClientRequestAction)
  <1>4. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm /\ H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm /\ ClientRequestAction => H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm' BY DEF TypeOK,H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm,ClientRequestAction,ClientRequest,H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,ExistsRequestVoteResponseQuorum
  \* (H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm /\ AdvanceCommitIndexAction => H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,ExistsRequestVoteResponseQuorum
  \* (H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,AppendEntriesAction)
  <1>6. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm /\ AppendEntriesAction => H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,ExistsRequestVoteResponseQuorum
  \* (H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_LogEntryInTermImpliesSafeAtTerm /\ H_CandidateInTermVotedForItself /\ H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm /\ HandleRequestVoteRequestAction => H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm' BY DEF TypeOK,H_LogEntryInTermImpliesSafeAtTerm,H_CandidateInTermVotedForItself,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,ExistsRequestVoteResponseQuorum
  \* (H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm /\ HandleRequestVoteResponseAction => H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,ExistsRequestVoteResponseQuorum
  \* (H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm /\ H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm /\ AcceptAppendEntriesRequestAppendAction => H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm' BY DEF TypeOK,H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,ExistsRequestVoteResponseQuorum
  \* (H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm /\ AcceptAppendEntriesRequestLearnCommitAction => H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,ExistsRequestVoteResponseQuorum
  \* (H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm /\ HandleAppendEntriesResponseAction => H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,ExistsRequestVoteResponseQuorum
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_LogEntryInTermImpliesSafeAtTerm
THEOREM L_20 == TypeOK /\ H_VoteInGrantedImpliesVotedFor /\ H_LeaderHasVotesGrantedQuorum /\ H_VoteGrantedImpliesNodeSafeAtTerm /\ H_CandidateInTermVotedForItself /\ H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ H_LogEntryInTermImpliesSafeAtTerm /\ Next => H_LogEntryInTermImpliesSafeAtTerm'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_LogEntryInTermImpliesSafeAtTerm,RequestVoteAction)
  <1>1. TypeOK /\ H_LogEntryInTermImpliesSafeAtTerm /\ RequestVoteAction => H_LogEntryInTermImpliesSafeAtTerm' BY DEF TypeOK,RequestVoteAction,RequestVote,H_LogEntryInTermImpliesSafeAtTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_LogEntryInTermImpliesSafeAtTerm,UpdateTermAction)
  <1>2. TypeOK /\ H_LogEntryInTermImpliesSafeAtTerm /\ UpdateTermAction => H_LogEntryInTermImpliesSafeAtTerm' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_LogEntryInTermImpliesSafeAtTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_LogEntryInTermImpliesSafeAtTerm,BecomeLeaderAction)
  <1>3. TypeOK /\ H_LogEntryInTermImpliesSafeAtTerm /\ BecomeLeaderAction => H_LogEntryInTermImpliesSafeAtTerm' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_LogEntryInTermImpliesSafeAtTerm
  \* (H_LogEntryInTermImpliesSafeAtTerm,ClientRequestAction)
  <1>4. TypeOK /\ H_VoteInGrantedImpliesVotedFor /\ H_LeaderHasVotesGrantedQuorum /\ H_VoteGrantedImpliesNodeSafeAtTerm /\ H_LogEntryInTermImpliesSafeAtTerm /\ ClientRequestAction => H_LogEntryInTermImpliesSafeAtTerm' BY DEF TypeOK,H_VoteInGrantedImpliesVotedFor,H_LeaderHasVotesGrantedQuorum,H_VoteGrantedImpliesNodeSafeAtTerm,ClientRequestAction,ClientRequest,H_LogEntryInTermImpliesSafeAtTerm
  \* (H_LogEntryInTermImpliesSafeAtTerm,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_LogEntryInTermImpliesSafeAtTerm /\ AdvanceCommitIndexAction => H_LogEntryInTermImpliesSafeAtTerm' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_LogEntryInTermImpliesSafeAtTerm
  \* (H_LogEntryInTermImpliesSafeAtTerm,AppendEntriesAction)
  <1>6. TypeOK /\ H_LogEntryInTermImpliesSafeAtTerm /\ AppendEntriesAction => H_LogEntryInTermImpliesSafeAtTerm' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_LogEntryInTermImpliesSafeAtTerm
  \* (H_LogEntryInTermImpliesSafeAtTerm,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_LogEntryInTermImpliesSafeAtTerm /\ HandleRequestVoteRequestAction => H_LogEntryInTermImpliesSafeAtTerm' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_LogEntryInTermImpliesSafeAtTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_LogEntryInTermImpliesSafeAtTerm,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_CandidateInTermVotedForItself /\ H_LogEntryInTermImpliesSafeAtTerm /\ HandleRequestVoteResponseAction => H_LogEntryInTermImpliesSafeAtTerm' BY DEF TypeOK,H_CandidateInTermVotedForItself,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_LogEntryInTermImpliesSafeAtTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_LogEntryInTermImpliesSafeAtTerm,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ H_LogEntryInTermImpliesSafeAtTerm /\ AcceptAppendEntriesRequestAppendAction => H_LogEntryInTermImpliesSafeAtTerm' BY DEF TypeOK,H_LogEntryInTermImpliesSafeAtTermAppendEntries,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_LogEntryInTermImpliesSafeAtTerm
  \* (H_LogEntryInTermImpliesSafeAtTerm,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_LogEntryInTermImpliesSafeAtTerm /\ AcceptAppendEntriesRequestLearnCommitAction => H_LogEntryInTermImpliesSafeAtTerm' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_LogEntryInTermImpliesSafeAtTerm
  \* (H_LogEntryInTermImpliesSafeAtTerm,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_LogEntryInTermImpliesSafeAtTerm /\ HandleAppendEntriesResponseAction => H_LogEntryInTermImpliesSafeAtTerm' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_LogEntryInTermImpliesSafeAtTerm
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_CandidateWithVotesGrantedInTermImplyNoOtherLeader
THEOREM L_21 == TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ H_LeaderHasVotesGrantedQuorum /\ H_VoteGrantedImpliesVoteResponseMsgConsistent /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLeader /\ Next => H_CandidateWithVotesGrantedInTermImplyNoOtherLeader'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,RequestVoteAction)
  <1>1. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLeader /\ RequestVoteAction => H_CandidateWithVotesGrantedInTermImplyNoOtherLeader' BY DEF TypeOK,RequestVoteAction,RequestVote,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,UpdateTermAction)
  <1>2. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLeader /\ UpdateTermAction => H_CandidateWithVotesGrantedInTermImplyNoOtherLeader' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,BecomeLeaderAction)
  <1>3. TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLeader /\ BecomeLeaderAction => H_CandidateWithVotesGrantedInTermImplyNoOtherLeader' BY DEF TypeOK,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,BecomeLeaderAction,BecomeLeader,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader
  \* (H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,ClientRequestAction)
  <1>4. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLeader /\ ClientRequestAction => H_CandidateWithVotesGrantedInTermImplyNoOtherLeader' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader
  \* (H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLeader /\ AdvanceCommitIndexAction => H_CandidateWithVotesGrantedInTermImplyNoOtherLeader' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader
  \* (H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,AppendEntriesAction)
  <1>6. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLeader /\ AppendEntriesAction => H_CandidateWithVotesGrantedInTermImplyNoOtherLeader' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader
  \* (H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLeader /\ HandleRequestVoteRequestAction => H_CandidateWithVotesGrantedInTermImplyNoOtherLeader' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ H_LeaderHasVotesGrantedQuorum /\ H_VoteGrantedImpliesVoteResponseMsgConsistent /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLeader /\ HandleRequestVoteResponseAction => H_CandidateWithVotesGrantedInTermImplyNoOtherLeader' BY DEF TypeOK,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,H_LeaderHasVotesGrantedQuorum,H_VoteGrantedImpliesVoteResponseMsgConsistent,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLeader /\ AcceptAppendEntriesRequestAppendAction => H_CandidateWithVotesGrantedInTermImplyNoOtherLeader' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader
  \* (H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLeader /\ AcceptAppendEntriesRequestLearnCommitAction => H_CandidateWithVotesGrantedInTermImplyNoOtherLeader' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader
  \* (H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLeader /\ HandleAppendEntriesResponseAction => H_CandidateWithVotesGrantedInTermImplyNoOtherLeader' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm
THEOREM L_22 == TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLeader /\ H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm /\ H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm /\ Next => H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm,RequestVoteAction)
  <1>1. TypeOK /\ H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm /\ RequestVoteAction => H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm' BY DEF TypeOK,RequestVoteAction,RequestVote,H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm,UpdateTermAction)
  <1>2. TypeOK /\ H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm /\ UpdateTermAction => H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm,BecomeLeaderAction)
  <1>3. TypeOK /\ H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm /\ BecomeLeaderAction => H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm
  \* (H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm,ClientRequestAction)
  <1>4. TypeOK /\ H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm /\ ClientRequestAction => H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm
  \* (H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm /\ AdvanceCommitIndexAction => H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm
  \* (H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm,AppendEntriesAction)
  <1>6. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLeader /\ H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm /\ AppendEntriesAction => H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm' BY DEF TypeOK,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,AppendEntriesAction,AppendEntries,H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm
  \* (H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm /\ HandleRequestVoteRequestAction => H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm /\ H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm /\ HandleRequestVoteResponseAction => H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm' BY DEF TypeOK,H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm /\ AcceptAppendEntriesRequestAppendAction => H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm
  \* (H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm /\ AcceptAppendEntriesRequestLearnCommitAction => H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm
  \* (H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm /\ HandleAppendEntriesResponseAction => H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_AppendEntriesRequestLogEntriesMustBeInLeaderLog
THEOREM L_23 == TypeOK /\ H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm /\ H_AppendEntriesRequestLogEntriesMustBeInLeaderLog /\ Next => H_AppendEntriesRequestLogEntriesMustBeInLeaderLog'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_AppendEntriesRequestLogEntriesMustBeInLeaderLog,RequestVoteAction)
  <1>1. TypeOK /\ H_AppendEntriesRequestLogEntriesMustBeInLeaderLog /\ RequestVoteAction => H_AppendEntriesRequestLogEntriesMustBeInLeaderLog' BY DEF TypeOK,RequestVoteAction,RequestVote,H_AppendEntriesRequestLogEntriesMustBeInLeaderLog,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_AppendEntriesRequestLogEntriesMustBeInLeaderLog,UpdateTermAction)
  <1>2. TypeOK /\ H_AppendEntriesRequestLogEntriesMustBeInLeaderLog /\ UpdateTermAction => H_AppendEntriesRequestLogEntriesMustBeInLeaderLog' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_AppendEntriesRequestLogEntriesMustBeInLeaderLog,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_AppendEntriesRequestLogEntriesMustBeInLeaderLog,BecomeLeaderAction)
  <1>3. TypeOK /\ H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm /\ H_AppendEntriesRequestLogEntriesMustBeInLeaderLog /\ BecomeLeaderAction => H_AppendEntriesRequestLogEntriesMustBeInLeaderLog' BY DEF TypeOK,H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm,BecomeLeaderAction,BecomeLeader,H_AppendEntriesRequestLogEntriesMustBeInLeaderLog
  \* (H_AppendEntriesRequestLogEntriesMustBeInLeaderLog,ClientRequestAction)
  <1>4. TypeOK /\ H_AppendEntriesRequestLogEntriesMustBeInLeaderLog /\ ClientRequestAction => H_AppendEntriesRequestLogEntriesMustBeInLeaderLog' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_AppendEntriesRequestLogEntriesMustBeInLeaderLog
  \* (H_AppendEntriesRequestLogEntriesMustBeInLeaderLog,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_AppendEntriesRequestLogEntriesMustBeInLeaderLog /\ AdvanceCommitIndexAction => H_AppendEntriesRequestLogEntriesMustBeInLeaderLog' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_AppendEntriesRequestLogEntriesMustBeInLeaderLog
  \* (H_AppendEntriesRequestLogEntriesMustBeInLeaderLog,AppendEntriesAction)
  <1>6. TypeOK /\ H_AppendEntriesRequestLogEntriesMustBeInLeaderLog /\ AppendEntriesAction => H_AppendEntriesRequestLogEntriesMustBeInLeaderLog' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_AppendEntriesRequestLogEntriesMustBeInLeaderLog
  \* (H_AppendEntriesRequestLogEntriesMustBeInLeaderLog,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_AppendEntriesRequestLogEntriesMustBeInLeaderLog /\ HandleRequestVoteRequestAction => H_AppendEntriesRequestLogEntriesMustBeInLeaderLog' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_AppendEntriesRequestLogEntriesMustBeInLeaderLog,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_AppendEntriesRequestLogEntriesMustBeInLeaderLog,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_AppendEntriesRequestLogEntriesMustBeInLeaderLog /\ HandleRequestVoteResponseAction => H_AppendEntriesRequestLogEntriesMustBeInLeaderLog' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_AppendEntriesRequestLogEntriesMustBeInLeaderLog,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_AppendEntriesRequestLogEntriesMustBeInLeaderLog,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_AppendEntriesRequestLogEntriesMustBeInLeaderLog /\ AcceptAppendEntriesRequestAppendAction => H_AppendEntriesRequestLogEntriesMustBeInLeaderLog' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_AppendEntriesRequestLogEntriesMustBeInLeaderLog
  \* (H_AppendEntriesRequestLogEntriesMustBeInLeaderLog,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_AppendEntriesRequestLogEntriesMustBeInLeaderLog /\ AcceptAppendEntriesRequestLearnCommitAction => H_AppendEntriesRequestLogEntriesMustBeInLeaderLog' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_AppendEntriesRequestLogEntriesMustBeInLeaderLog
  \* (H_AppendEntriesRequestLogEntriesMustBeInLeaderLog,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_AppendEntriesRequestLogEntriesMustBeInLeaderLog /\ HandleAppendEntriesResponseAction => H_AppendEntriesRequestLogEntriesMustBeInLeaderLog' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_AppendEntriesRequestLogEntriesMustBeInLeaderLog
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_LogMatchingBetweenAppendEntriesMsgs
THEOREM L_24 == TypeOK /\ H_LogMatching /\ H_LogMatchingAppendEntries /\ H_LogMatchingBetweenAppendEntriesMsgs /\ Next => H_LogMatchingBetweenAppendEntriesMsgs'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_LogMatchingBetweenAppendEntriesMsgs,RequestVoteAction)
  <1>1. TypeOK /\ H_LogMatchingBetweenAppendEntriesMsgs /\ RequestVoteAction => H_LogMatchingBetweenAppendEntriesMsgs' BY DEF TypeOK,RequestVoteAction,RequestVote,H_LogMatchingBetweenAppendEntriesMsgs,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_LogMatchingBetweenAppendEntriesMsgs,UpdateTermAction)
  <1>2. TypeOK /\ H_LogMatchingBetweenAppendEntriesMsgs /\ UpdateTermAction => H_LogMatchingBetweenAppendEntriesMsgs' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_LogMatchingBetweenAppendEntriesMsgs,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_LogMatchingBetweenAppendEntriesMsgs,BecomeLeaderAction)
  <1>3. TypeOK /\ H_LogMatchingBetweenAppendEntriesMsgs /\ BecomeLeaderAction => H_LogMatchingBetweenAppendEntriesMsgs' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_LogMatchingBetweenAppendEntriesMsgs
  \* (H_LogMatchingBetweenAppendEntriesMsgs,ClientRequestAction)
  <1>4. TypeOK /\ H_LogMatchingBetweenAppendEntriesMsgs /\ ClientRequestAction => H_LogMatchingBetweenAppendEntriesMsgs' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_LogMatchingBetweenAppendEntriesMsgs
  \* (H_LogMatchingBetweenAppendEntriesMsgs,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_LogMatchingBetweenAppendEntriesMsgs /\ AdvanceCommitIndexAction => H_LogMatchingBetweenAppendEntriesMsgs' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_LogMatchingBetweenAppendEntriesMsgs
  \* (H_LogMatchingBetweenAppendEntriesMsgs,AppendEntriesAction)
  <1>6. TypeOK /\ H_LogMatching /\ H_LogMatchingAppendEntries /\ H_LogMatchingBetweenAppendEntriesMsgs /\ AppendEntriesAction => H_LogMatchingBetweenAppendEntriesMsgs' BY DEF TypeOK,H_LogMatching,H_LogMatchingAppendEntries,AppendEntriesAction,AppendEntries,H_LogMatchingBetweenAppendEntriesMsgs
  \* (H_LogMatchingBetweenAppendEntriesMsgs,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_LogMatchingBetweenAppendEntriesMsgs /\ HandleRequestVoteRequestAction => H_LogMatchingBetweenAppendEntriesMsgs' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_LogMatchingBetweenAppendEntriesMsgs,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_LogMatchingBetweenAppendEntriesMsgs,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_LogMatchingBetweenAppendEntriesMsgs /\ HandleRequestVoteResponseAction => H_LogMatchingBetweenAppendEntriesMsgs' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_LogMatchingBetweenAppendEntriesMsgs,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_LogMatchingBetweenAppendEntriesMsgs,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_LogMatchingBetweenAppendEntriesMsgs /\ AcceptAppendEntriesRequestAppendAction => H_LogMatchingBetweenAppendEntriesMsgs' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_LogMatchingBetweenAppendEntriesMsgs
  \* (H_LogMatchingBetweenAppendEntriesMsgs,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_LogMatchingBetweenAppendEntriesMsgs /\ AcceptAppendEntriesRequestLearnCommitAction => H_LogMatchingBetweenAppendEntriesMsgs' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_LogMatchingBetweenAppendEntriesMsgs
  \* (H_LogMatchingBetweenAppendEntriesMsgs,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_LogMatchingBetweenAppendEntriesMsgs /\ HandleAppendEntriesResponseAction => H_LogMatchingBetweenAppendEntriesMsgs' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_LogMatchingBetweenAppendEntriesMsgs
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_LogMatchingInAppendEntriesMsgsLeaders
THEOREM L_25 == TypeOK /\ H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm /\ H_LogMatching /\ H_PrimaryHasEntriesItCreated /\ H_LogMatchingInAppendEntriesMsgsLeaders /\ Next => H_LogMatchingInAppendEntriesMsgsLeaders'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_LogMatchingInAppendEntriesMsgsLeaders,RequestVoteAction)
  <1>1. TypeOK /\ H_LogMatchingInAppendEntriesMsgsLeaders /\ RequestVoteAction => H_LogMatchingInAppendEntriesMsgsLeaders' BY DEF TypeOK,RequestVoteAction,RequestVote,H_LogMatchingInAppendEntriesMsgsLeaders,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_LogMatchingInAppendEntriesMsgsLeaders,UpdateTermAction)
  <1>2. TypeOK /\ H_LogMatchingInAppendEntriesMsgsLeaders /\ UpdateTermAction => H_LogMatchingInAppendEntriesMsgsLeaders' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_LogMatchingInAppendEntriesMsgsLeaders,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_LogMatchingInAppendEntriesMsgsLeaders,BecomeLeaderAction)
  <1>3. TypeOK /\ H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm /\ H_LogMatchingInAppendEntriesMsgsLeaders /\ BecomeLeaderAction => H_LogMatchingInAppendEntriesMsgsLeaders' BY DEF TypeOK,H_LogEntryInTermImpliesSafeAtTermAppendEntries,H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm,BecomeLeaderAction,BecomeLeader,H_LogMatchingInAppendEntriesMsgsLeaders
  \* (H_LogMatchingInAppendEntriesMsgsLeaders,ClientRequestAction)
  <1>4. TypeOK /\ H_LogMatchingInAppendEntriesMsgsLeaders /\ ClientRequestAction => H_LogMatchingInAppendEntriesMsgsLeaders' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_LogMatchingInAppendEntriesMsgsLeaders
  \* (H_LogMatchingInAppendEntriesMsgsLeaders,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_LogMatchingInAppendEntriesMsgsLeaders /\ AdvanceCommitIndexAction => H_LogMatchingInAppendEntriesMsgsLeaders' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_LogMatchingInAppendEntriesMsgsLeaders
  \* (H_LogMatchingInAppendEntriesMsgsLeaders,AppendEntriesAction)
  <1>6. TypeOK /\ H_LogMatching /\ H_PrimaryHasEntriesItCreated /\ H_LogMatchingInAppendEntriesMsgsLeaders /\ AppendEntriesAction => H_LogMatchingInAppendEntriesMsgsLeaders' BY DEF TypeOK,H_LogMatching,H_PrimaryHasEntriesItCreated,AppendEntriesAction,AppendEntries,H_LogMatchingInAppendEntriesMsgsLeaders
  \* (H_LogMatchingInAppendEntriesMsgsLeaders,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_LogMatchingInAppendEntriesMsgsLeaders /\ HandleRequestVoteRequestAction => H_LogMatchingInAppendEntriesMsgsLeaders' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_LogMatchingInAppendEntriesMsgsLeaders,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_LogMatchingInAppendEntriesMsgsLeaders,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_LogMatchingInAppendEntriesMsgsLeaders /\ HandleRequestVoteResponseAction => H_LogMatchingInAppendEntriesMsgsLeaders' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_LogMatchingInAppendEntriesMsgsLeaders,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_LogMatchingInAppendEntriesMsgsLeaders,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_LogMatchingInAppendEntriesMsgsLeaders /\ AcceptAppendEntriesRequestAppendAction => H_LogMatchingInAppendEntriesMsgsLeaders' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_LogMatchingInAppendEntriesMsgsLeaders
  \* (H_LogMatchingInAppendEntriesMsgsLeaders,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_LogMatchingInAppendEntriesMsgsLeaders /\ AcceptAppendEntriesRequestLearnCommitAction => H_LogMatchingInAppendEntriesMsgsLeaders' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_LogMatchingInAppendEntriesMsgsLeaders
  \* (H_LogMatchingInAppendEntriesMsgsLeaders,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_LogMatchingInAppendEntriesMsgsLeaders /\ HandleAppendEntriesResponseAction => H_LogMatchingInAppendEntriesMsgsLeaders' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_LogMatchingInAppendEntriesMsgsLeaders
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_PrimaryHasEntriesItCreatedAppendEntries
THEOREM L_26 == TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm /\ H_PrimaryHasEntriesItCreated /\ H_PrimaryHasEntriesItCreatedAppendEntries /\ Next => H_PrimaryHasEntriesItCreatedAppendEntries'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_PrimaryHasEntriesItCreatedAppendEntries,RequestVoteAction)
  <1>1. TypeOK /\ H_PrimaryHasEntriesItCreatedAppendEntries /\ RequestVoteAction => H_PrimaryHasEntriesItCreatedAppendEntries' BY DEF TypeOK,RequestVoteAction,RequestVote,H_PrimaryHasEntriesItCreatedAppendEntries,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_PrimaryHasEntriesItCreatedAppendEntries,UpdateTermAction)
  <1>2. TypeOK /\ H_PrimaryHasEntriesItCreatedAppendEntries /\ UpdateTermAction => H_PrimaryHasEntriesItCreatedAppendEntries' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_PrimaryHasEntriesItCreatedAppendEntries,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_PrimaryHasEntriesItCreatedAppendEntries,BecomeLeaderAction)
  <1>3. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm /\ H_PrimaryHasEntriesItCreatedAppendEntries /\ BecomeLeaderAction => H_PrimaryHasEntriesItCreatedAppendEntries' BY DEF TypeOK,H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm,BecomeLeaderAction,BecomeLeader,H_PrimaryHasEntriesItCreatedAppendEntries
  \* (H_PrimaryHasEntriesItCreatedAppendEntries,ClientRequestAction)
  <1>4. TypeOK /\ H_PrimaryHasEntriesItCreatedAppendEntries /\ ClientRequestAction => H_PrimaryHasEntriesItCreatedAppendEntries' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_PrimaryHasEntriesItCreatedAppendEntries
  \* (H_PrimaryHasEntriesItCreatedAppendEntries,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_PrimaryHasEntriesItCreatedAppendEntries /\ AdvanceCommitIndexAction => H_PrimaryHasEntriesItCreatedAppendEntries' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_PrimaryHasEntriesItCreatedAppendEntries
  \* (H_PrimaryHasEntriesItCreatedAppendEntries,AppendEntriesAction)
  <1>6. TypeOK /\ H_PrimaryHasEntriesItCreated /\ H_PrimaryHasEntriesItCreatedAppendEntries /\ AppendEntriesAction => H_PrimaryHasEntriesItCreatedAppendEntries' BY DEF TypeOK,H_PrimaryHasEntriesItCreated,AppendEntriesAction,AppendEntries,H_PrimaryHasEntriesItCreatedAppendEntries
  \* (H_PrimaryHasEntriesItCreatedAppendEntries,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_PrimaryHasEntriesItCreatedAppendEntries /\ HandleRequestVoteRequestAction => H_PrimaryHasEntriesItCreatedAppendEntries' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_PrimaryHasEntriesItCreatedAppendEntries,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_PrimaryHasEntriesItCreatedAppendEntries,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_PrimaryHasEntriesItCreatedAppendEntries /\ HandleRequestVoteResponseAction => H_PrimaryHasEntriesItCreatedAppendEntries' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_PrimaryHasEntriesItCreatedAppendEntries,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_PrimaryHasEntriesItCreatedAppendEntries,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_PrimaryHasEntriesItCreatedAppendEntries /\ AcceptAppendEntriesRequestAppendAction => H_PrimaryHasEntriesItCreatedAppendEntries' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_PrimaryHasEntriesItCreatedAppendEntries
  \* (H_PrimaryHasEntriesItCreatedAppendEntries,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_PrimaryHasEntriesItCreatedAppendEntries /\ AcceptAppendEntriesRequestLearnCommitAction => H_PrimaryHasEntriesItCreatedAppendEntries' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_PrimaryHasEntriesItCreatedAppendEntries
  \* (H_PrimaryHasEntriesItCreatedAppendEntries,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_PrimaryHasEntriesItCreatedAppendEntries /\ HandleAppendEntriesResponseAction => H_PrimaryHasEntriesItCreatedAppendEntries' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_PrimaryHasEntriesItCreatedAppendEntries
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm
THEOREM L_27 == TypeOK /\ H_LogEntryInTermImpliesSafeAtTerm /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLeader /\ H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm /\ H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm /\ Next => H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm,RequestVoteAction)
  <1>1. TypeOK /\ H_LogEntryInTermImpliesSafeAtTerm /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm /\ RequestVoteAction => H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm' BY DEF TypeOK,H_LogEntryInTermImpliesSafeAtTerm,RequestVoteAction,RequestVote,H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm,UpdateTermAction)
  <1>2. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm /\ UpdateTermAction => H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm,BecomeLeaderAction)
  <1>3. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm /\ BecomeLeaderAction => H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm
  \* (H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm,ClientRequestAction)
  <1>4. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLeader /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm /\ ClientRequestAction => H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm' BY DEF TypeOK,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,ClientRequestAction,ClientRequest,H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm
  \* (H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm /\ AdvanceCommitIndexAction => H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm
  \* (H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm,AppendEntriesAction)
  <1>6. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm /\ AppendEntriesAction => H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm
  \* (H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm /\ HandleRequestVoteRequestAction => H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm /\ HandleRequestVoteResponseAction => H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm' BY DEF TypeOK,H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm /\ AcceptAppendEntriesRequestAppendAction => H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm' BY DEF TypeOK,H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm
  \* (H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm /\ AcceptAppendEntriesRequestLearnCommitAction => H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm
  \* (H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm /\ HandleAppendEntriesResponseAction => H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_OnePrimaryPerTerm
THEOREM L_28 == TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLeader /\ H_OnePrimaryPerTerm /\ Next => H_OnePrimaryPerTerm'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_OnePrimaryPerTerm,RequestVoteAction)
  <1>1. TypeOK /\ H_OnePrimaryPerTerm /\ RequestVoteAction => H_OnePrimaryPerTerm' BY DEF TypeOK,RequestVoteAction,RequestVote,H_OnePrimaryPerTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_OnePrimaryPerTerm,UpdateTermAction)
  <1>2. TypeOK /\ H_OnePrimaryPerTerm /\ UpdateTermAction => H_OnePrimaryPerTerm' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_OnePrimaryPerTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_OnePrimaryPerTerm,BecomeLeaderAction)
  <1>3. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLeader /\ H_OnePrimaryPerTerm /\ BecomeLeaderAction => H_OnePrimaryPerTerm' BY DEF TypeOK,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,BecomeLeaderAction,BecomeLeader,H_OnePrimaryPerTerm
  \* (H_OnePrimaryPerTerm,ClientRequestAction)
  <1>4. TypeOK /\ H_OnePrimaryPerTerm /\ ClientRequestAction => H_OnePrimaryPerTerm' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_OnePrimaryPerTerm
  \* (H_OnePrimaryPerTerm,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_OnePrimaryPerTerm /\ AdvanceCommitIndexAction => H_OnePrimaryPerTerm' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_OnePrimaryPerTerm
  \* (H_OnePrimaryPerTerm,AppendEntriesAction)
  <1>6. TypeOK /\ H_OnePrimaryPerTerm /\ AppendEntriesAction => H_OnePrimaryPerTerm' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_OnePrimaryPerTerm
  \* (H_OnePrimaryPerTerm,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_OnePrimaryPerTerm /\ HandleRequestVoteRequestAction => H_OnePrimaryPerTerm' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_OnePrimaryPerTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_OnePrimaryPerTerm,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_OnePrimaryPerTerm /\ HandleRequestVoteResponseAction => H_OnePrimaryPerTerm' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_OnePrimaryPerTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_OnePrimaryPerTerm,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_OnePrimaryPerTerm /\ AcceptAppendEntriesRequestAppendAction => H_OnePrimaryPerTerm' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_OnePrimaryPerTerm
  \* (H_OnePrimaryPerTerm,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_OnePrimaryPerTerm /\ AcceptAppendEntriesRequestLearnCommitAction => H_OnePrimaryPerTerm' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_OnePrimaryPerTerm
  \* (H_OnePrimaryPerTerm,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_OnePrimaryPerTerm /\ HandleAppendEntriesResponseAction => H_OnePrimaryPerTerm' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_OnePrimaryPerTerm
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_LeaderMatchIndexValidAppendEntries
THEOREM L_29 == TypeOK /\ H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm /\ H_AppendEntriesRequestLogEntriesMustBeInLeaderLog /\ H_LeaderMatchIndexValidAppendEntries /\ Next => H_LeaderMatchIndexValidAppendEntries'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_LeaderMatchIndexValidAppendEntries,RequestVoteAction)
  <1>1. TypeOK /\ H_LeaderMatchIndexValidAppendEntries /\ RequestVoteAction => H_LeaderMatchIndexValidAppendEntries' BY DEF TypeOK,RequestVoteAction,RequestVote,H_LeaderMatchIndexValidAppendEntries,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_LeaderMatchIndexValidAppendEntries,UpdateTermAction)
  <1>2. TypeOK /\ H_LeaderMatchIndexValidAppendEntries /\ UpdateTermAction => H_LeaderMatchIndexValidAppendEntries' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_LeaderMatchIndexValidAppendEntries,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_LeaderMatchIndexValidAppendEntries,BecomeLeaderAction)
  <1>3. TypeOK /\ H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm /\ H_LeaderMatchIndexValidAppendEntries /\ BecomeLeaderAction => H_LeaderMatchIndexValidAppendEntries' BY DEF TypeOK,H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm,BecomeLeaderAction,BecomeLeader,H_LeaderMatchIndexValidAppendEntries
  \* (H_LeaderMatchIndexValidAppendEntries,ClientRequestAction)
  <1>4. TypeOK /\ H_LeaderMatchIndexValidAppendEntries /\ ClientRequestAction => H_LeaderMatchIndexValidAppendEntries' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_LeaderMatchIndexValidAppendEntries
  \* (H_LeaderMatchIndexValidAppendEntries,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_LeaderMatchIndexValidAppendEntries /\ AdvanceCommitIndexAction => H_LeaderMatchIndexValidAppendEntries' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_LeaderMatchIndexValidAppendEntries
  \* (H_LeaderMatchIndexValidAppendEntries,AppendEntriesAction)
  <1>6. TypeOK /\ H_LeaderMatchIndexValidAppendEntries /\ AppendEntriesAction => H_LeaderMatchIndexValidAppendEntries' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_LeaderMatchIndexValidAppendEntries
  \* (H_LeaderMatchIndexValidAppendEntries,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_LeaderMatchIndexValidAppendEntries /\ HandleRequestVoteRequestAction => H_LeaderMatchIndexValidAppendEntries' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_LeaderMatchIndexValidAppendEntries,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_LeaderMatchIndexValidAppendEntries,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_LeaderMatchIndexValidAppendEntries /\ HandleRequestVoteResponseAction => H_LeaderMatchIndexValidAppendEntries' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_LeaderMatchIndexValidAppendEntries,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_LeaderMatchIndexValidAppendEntries,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_AppendEntriesRequestLogEntriesMustBeInLeaderLog /\ H_LeaderMatchIndexValidAppendEntries /\ AcceptAppendEntriesRequestAppendAction => H_LeaderMatchIndexValidAppendEntries' BY DEF TypeOK,H_AppendEntriesRequestLogEntriesMustBeInLeaderLog,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_LeaderMatchIndexValidAppendEntries
  \* (H_LeaderMatchIndexValidAppendEntries,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_LeaderMatchIndexValidAppendEntries /\ AcceptAppendEntriesRequestLearnCommitAction => H_LeaderMatchIndexValidAppendEntries' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_LeaderMatchIndexValidAppendEntries
  \* (H_LeaderMatchIndexValidAppendEntries,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_LeaderMatchIndexValidAppendEntries /\ HandleAppendEntriesResponseAction => H_LeaderMatchIndexValidAppendEntries' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_LeaderMatchIndexValidAppendEntries
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_LeaderMatchIndexBound
THEOREM L_30 == TypeOK /\ H_LeaderMatchIndexValidAppendEntries /\ H_LeaderMatchIndexBound /\ Next => H_LeaderMatchIndexBound'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_LeaderMatchIndexBound,RequestVoteAction)
  <1>1. TypeOK /\ H_LeaderMatchIndexBound /\ RequestVoteAction => H_LeaderMatchIndexBound' BY DEF TypeOK,RequestVoteAction,RequestVote,H_LeaderMatchIndexBound,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_LeaderMatchIndexBound,UpdateTermAction)
  <1>2. TypeOK /\ H_LeaderMatchIndexBound /\ UpdateTermAction => H_LeaderMatchIndexBound' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_LeaderMatchIndexBound,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_LeaderMatchIndexBound,BecomeLeaderAction)
  <1>3. TypeOK /\ H_LeaderMatchIndexBound /\ BecomeLeaderAction => H_LeaderMatchIndexBound' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_LeaderMatchIndexBound
  \* (H_LeaderMatchIndexBound,ClientRequestAction)
  <1>4. TypeOK /\ H_LeaderMatchIndexBound /\ ClientRequestAction => H_LeaderMatchIndexBound' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_LeaderMatchIndexBound
  \* (H_LeaderMatchIndexBound,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_LeaderMatchIndexBound /\ AdvanceCommitIndexAction => H_LeaderMatchIndexBound' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_LeaderMatchIndexBound
  \* (H_LeaderMatchIndexBound,AppendEntriesAction)
  <1>6. TypeOK /\ H_LeaderMatchIndexBound /\ AppendEntriesAction => H_LeaderMatchIndexBound' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_LeaderMatchIndexBound
  \* (H_LeaderMatchIndexBound,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_LeaderMatchIndexBound /\ HandleRequestVoteRequestAction => H_LeaderMatchIndexBound' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_LeaderMatchIndexBound,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_LeaderMatchIndexBound,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_LeaderMatchIndexBound /\ HandleRequestVoteResponseAction => H_LeaderMatchIndexBound' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_LeaderMatchIndexBound,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_LeaderMatchIndexBound,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_LeaderMatchIndexBound /\ AcceptAppendEntriesRequestAppendAction => H_LeaderMatchIndexBound' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_LeaderMatchIndexBound
  \* (H_LeaderMatchIndexBound,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_LeaderMatchIndexBound /\ AcceptAppendEntriesRequestLearnCommitAction => H_LeaderMatchIndexBound' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_LeaderMatchIndexBound
  \* (H_LeaderMatchIndexBound,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_LeaderMatchIndexValidAppendEntries /\ H_LeaderMatchIndexBound /\ HandleAppendEntriesResponseAction => H_LeaderMatchIndexBound' BY DEF TypeOK,H_LeaderMatchIndexValidAppendEntries,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_LeaderMatchIndexBound
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_LogMatchingAppendEntries
THEOREM L_31 == TypeOK /\ H_LogMatchingInAppendEntriesMsgsLeaders /\ H_LogMatching /\ H_LogMatchingBetweenAppendEntriesMsgs /\ H_LogMatchingAppendEntries /\ Next => H_LogMatchingAppendEntries'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_LogMatchingAppendEntries,RequestVoteAction)
  <1>1. TypeOK /\ H_LogMatchingAppendEntries /\ RequestVoteAction => H_LogMatchingAppendEntries' BY DEF TypeOK,RequestVoteAction,RequestVote,H_LogMatchingAppendEntries,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_LogMatchingAppendEntries,UpdateTermAction)
  <1>2. TypeOK /\ H_LogMatchingAppendEntries /\ UpdateTermAction => H_LogMatchingAppendEntries' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_LogMatchingAppendEntries,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_LogMatchingAppendEntries,BecomeLeaderAction)
  <1>3. TypeOK /\ H_LogMatchingAppendEntries /\ BecomeLeaderAction => H_LogMatchingAppendEntries' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_LogMatchingAppendEntries
  \* (H_LogMatchingAppendEntries,ClientRequestAction)
  <1>4. TypeOK /\ H_LogMatchingInAppendEntriesMsgsLeaders /\ H_LogMatchingAppendEntries /\ ClientRequestAction => H_LogMatchingAppendEntries' BY DEF TypeOK,H_LogMatchingInAppendEntriesMsgsLeaders,ClientRequestAction,ClientRequest,H_LogMatchingAppendEntries
  \* (H_LogMatchingAppendEntries,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_LogMatchingAppendEntries /\ AdvanceCommitIndexAction => H_LogMatchingAppendEntries' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_LogMatchingAppendEntries
  \* (H_LogMatchingAppendEntries,AppendEntriesAction)
  <1>6. TypeOK /\ H_LogMatching /\ H_LogMatchingAppendEntries /\ AppendEntriesAction => H_LogMatchingAppendEntries' BY DEF TypeOK,H_LogMatching,AppendEntriesAction,AppendEntries,H_LogMatchingAppendEntries
  \* (H_LogMatchingAppendEntries,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_LogMatchingAppendEntries /\ HandleRequestVoteRequestAction => H_LogMatchingAppendEntries' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_LogMatchingAppendEntries,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_LogMatchingAppendEntries,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_LogMatchingAppendEntries /\ HandleRequestVoteResponseAction => H_LogMatchingAppendEntries' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_LogMatchingAppendEntries,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_LogMatchingAppendEntries,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_LogMatchingBetweenAppendEntriesMsgs /\ H_LogMatchingAppendEntries /\ AcceptAppendEntriesRequestAppendAction => H_LogMatchingAppendEntries' BY DEF TypeOK,H_LogMatchingBetweenAppendEntriesMsgs,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_LogMatchingAppendEntries
  \* (H_LogMatchingAppendEntries,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_LogMatchingAppendEntries /\ AcceptAppendEntriesRequestLearnCommitAction => H_LogMatchingAppendEntries' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_LogMatchingAppendEntries
  \* (H_LogMatchingAppendEntries,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_LogMatchingAppendEntries /\ HandleAppendEntriesResponseAction => H_LogMatchingAppendEntries' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_LogMatchingAppendEntries
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_PrimaryHasEntriesItCreated
THEOREM L_32 == TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm /\ H_OnePrimaryPerTerm /\ H_PrimaryHasEntriesItCreatedAppendEntries /\ H_PrimaryHasEntriesItCreated /\ Next => H_PrimaryHasEntriesItCreated'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_PrimaryHasEntriesItCreated,RequestVoteAction)
  <1>1. TypeOK /\ H_PrimaryHasEntriesItCreated /\ RequestVoteAction => H_PrimaryHasEntriesItCreated' BY DEF TypeOK,RequestVoteAction,RequestVote,H_PrimaryHasEntriesItCreated,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_PrimaryHasEntriesItCreated,UpdateTermAction)
  <1>2. TypeOK /\ H_PrimaryHasEntriesItCreated /\ UpdateTermAction => H_PrimaryHasEntriesItCreated' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_PrimaryHasEntriesItCreated,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_PrimaryHasEntriesItCreated,BecomeLeaderAction)
  <1>3. TypeOK /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm /\ H_PrimaryHasEntriesItCreated /\ BecomeLeaderAction => H_PrimaryHasEntriesItCreated' BY DEF TypeOK,H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm,BecomeLeaderAction,BecomeLeader,H_PrimaryHasEntriesItCreated
  \* (H_PrimaryHasEntriesItCreated,ClientRequestAction)
  <1>4. TypeOK /\ H_OnePrimaryPerTerm /\ H_PrimaryHasEntriesItCreated /\ ClientRequestAction => H_PrimaryHasEntriesItCreated' BY DEF TypeOK,H_OnePrimaryPerTerm,ClientRequestAction,ClientRequest,H_PrimaryHasEntriesItCreated
  \* (H_PrimaryHasEntriesItCreated,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_PrimaryHasEntriesItCreated /\ AdvanceCommitIndexAction => H_PrimaryHasEntriesItCreated' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_PrimaryHasEntriesItCreated
  \* (H_PrimaryHasEntriesItCreated,AppendEntriesAction)
  <1>6. TypeOK /\ H_PrimaryHasEntriesItCreated /\ AppendEntriesAction => H_PrimaryHasEntriesItCreated' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_PrimaryHasEntriesItCreated
  \* (H_PrimaryHasEntriesItCreated,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_PrimaryHasEntriesItCreated /\ HandleRequestVoteRequestAction => H_PrimaryHasEntriesItCreated' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_PrimaryHasEntriesItCreated,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_PrimaryHasEntriesItCreated,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_PrimaryHasEntriesItCreated /\ HandleRequestVoteResponseAction => H_PrimaryHasEntriesItCreated' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_PrimaryHasEntriesItCreated,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_PrimaryHasEntriesItCreated,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_PrimaryHasEntriesItCreatedAppendEntries /\ H_PrimaryHasEntriesItCreated /\ AcceptAppendEntriesRequestAppendAction => H_PrimaryHasEntriesItCreated' BY DEF TypeOK,H_PrimaryHasEntriesItCreatedAppendEntries,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_PrimaryHasEntriesItCreated
  \* (H_PrimaryHasEntriesItCreated,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_PrimaryHasEntriesItCreated /\ AcceptAppendEntriesRequestLearnCommitAction => H_PrimaryHasEntriesItCreated' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_PrimaryHasEntriesItCreated
  \* (H_PrimaryHasEntriesItCreated,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_PrimaryHasEntriesItCreated /\ HandleAppendEntriesResponseAction => H_PrimaryHasEntriesItCreated' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_PrimaryHasEntriesItCreated
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_CommitIndexBoundValid
THEOREM L_33 == TypeOK /\ H_CommitIndexBoundValid /\ Next => H_CommitIndexBoundValid'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_CommitIndexBoundValid,RequestVoteAction)
  <1>1. TypeOK /\ H_CommitIndexBoundValid /\ RequestVoteAction => H_CommitIndexBoundValid' BY DEF TypeOK,RequestVoteAction,RequestVote,H_CommitIndexBoundValid,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_CommitIndexBoundValid,UpdateTermAction)
  <1>2. TypeOK /\ H_CommitIndexBoundValid /\ UpdateTermAction => H_CommitIndexBoundValid' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_CommitIndexBoundValid,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_CommitIndexBoundValid,BecomeLeaderAction)
  <1>3. TypeOK /\ H_CommitIndexBoundValid /\ BecomeLeaderAction => H_CommitIndexBoundValid' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_CommitIndexBoundValid
  \* (H_CommitIndexBoundValid,ClientRequestAction)
  <1>4. TypeOK /\ H_CommitIndexBoundValid /\ ClientRequestAction => H_CommitIndexBoundValid' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_CommitIndexBoundValid
  \* (H_CommitIndexBoundValid,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_CommitIndexBoundValid /\ AdvanceCommitIndexAction => H_CommitIndexBoundValid' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_CommitIndexBoundValid
  \* (H_CommitIndexBoundValid,AppendEntriesAction)
  <1>6. TypeOK /\ H_CommitIndexBoundValid /\ AppendEntriesAction => H_CommitIndexBoundValid' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_CommitIndexBoundValid
  \* (H_CommitIndexBoundValid,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_CommitIndexBoundValid /\ HandleRequestVoteRequestAction => H_CommitIndexBoundValid' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_CommitIndexBoundValid,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_CommitIndexBoundValid,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_CommitIndexBoundValid /\ HandleRequestVoteResponseAction => H_CommitIndexBoundValid' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_CommitIndexBoundValid,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_CommitIndexBoundValid,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_CommitIndexBoundValid /\ AcceptAppendEntriesRequestAppendAction => H_CommitIndexBoundValid' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_CommitIndexBoundValid
  \* (H_CommitIndexBoundValid,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_CommitIndexBoundValid /\ AcceptAppendEntriesRequestLearnCommitAction => H_CommitIndexBoundValid' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_CommitIndexBoundValid
  \* (H_CommitIndexBoundValid,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_CommitIndexBoundValid /\ HandleAppendEntriesResponseAction => H_CommitIndexBoundValid' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_CommitIndexBoundValid
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_CommitIndexCoveredOnQuorum
THEOREM L_34 == TypeOK /\ H_LeaderMatchIndexValid /\ H_CommitIndexInAppendEntriesImpliesCommittedEntryExists /\ H_LogMatching /\ H_CommitIndexCoveredOnQuorum /\ Next => H_CommitIndexCoveredOnQuorum'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_CommitIndexCoveredOnQuorum,RequestVoteAction)
  <1>1. TypeOK /\ H_CommitIndexCoveredOnQuorum /\ RequestVoteAction => H_CommitIndexCoveredOnQuorum' BY DEF TypeOK,RequestVoteAction,RequestVote,H_CommitIndexCoveredOnQuorum,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_CommitIndexCoveredOnQuorum,UpdateTermAction)
  <1>2. TypeOK /\ H_CommitIndexCoveredOnQuorum /\ UpdateTermAction => H_CommitIndexCoveredOnQuorum' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_CommitIndexCoveredOnQuorum,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_CommitIndexCoveredOnQuorum,BecomeLeaderAction)
  <1>3. TypeOK /\ H_CommitIndexCoveredOnQuorum /\ BecomeLeaderAction => H_CommitIndexCoveredOnQuorum' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_CommitIndexCoveredOnQuorum
  \* (H_CommitIndexCoveredOnQuorum,ClientRequestAction)
  <1>4. TypeOK /\ H_CommitIndexCoveredOnQuorum /\ ClientRequestAction => H_CommitIndexCoveredOnQuorum' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_CommitIndexCoveredOnQuorum
  \* (H_CommitIndexCoveredOnQuorum,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_LeaderMatchIndexValid /\ H_CommitIndexCoveredOnQuorum /\ AdvanceCommitIndexAction => H_CommitIndexCoveredOnQuorum' BY DEF TypeOK,H_LeaderMatchIndexValid,AdvanceCommitIndexAction,AdvanceCommitIndex,H_CommitIndexCoveredOnQuorum
  \* (H_CommitIndexCoveredOnQuorum,AppendEntriesAction)
  <1>6. TypeOK /\ H_CommitIndexCoveredOnQuorum /\ AppendEntriesAction => H_CommitIndexCoveredOnQuorum' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_CommitIndexCoveredOnQuorum
  \* (H_CommitIndexCoveredOnQuorum,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_CommitIndexCoveredOnQuorum /\ HandleRequestVoteRequestAction => H_CommitIndexCoveredOnQuorum' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_CommitIndexCoveredOnQuorum,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_CommitIndexCoveredOnQuorum,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_CommitIndexCoveredOnQuorum /\ HandleRequestVoteResponseAction => H_CommitIndexCoveredOnQuorum' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_CommitIndexCoveredOnQuorum,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_CommitIndexCoveredOnQuorum,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_CommitIndexCoveredOnQuorum /\ AcceptAppendEntriesRequestAppendAction => H_CommitIndexCoveredOnQuorum' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_CommitIndexCoveredOnQuorum
  \* (H_CommitIndexCoveredOnQuorum,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_CommitIndexInAppendEntriesImpliesCommittedEntryExists /\ H_LogMatching /\ H_CommitIndexCoveredOnQuorum /\ AcceptAppendEntriesRequestLearnCommitAction => H_CommitIndexCoveredOnQuorum' BY DEF TypeOK,H_CommitIndexInAppendEntriesImpliesCommittedEntryExists,H_LogMatching,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_CommitIndexCoveredOnQuorum
  \* (H_CommitIndexCoveredOnQuorum,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_CommitIndexCoveredOnQuorum /\ HandleAppendEntriesResponseAction => H_CommitIndexCoveredOnQuorum' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_CommitIndexCoveredOnQuorum
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_LeaderMatchIndexValid
THEOREM L_35 == TypeOK /\ H_LeaderMatchIndexBound /\ H_LeaderMatchIndexValidAppendEntries /\ H_LogMatching /\ H_LeaderMatchIndexValid /\ Next => H_LeaderMatchIndexValid'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_LeaderMatchIndexValid,RequestVoteAction)
  <1>1. TypeOK /\ H_LeaderMatchIndexValid /\ RequestVoteAction => H_LeaderMatchIndexValid' BY DEF TypeOK,RequestVoteAction,RequestVote,H_LeaderMatchIndexValid,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_LeaderMatchIndexValid,UpdateTermAction)
  <1>2. TypeOK /\ H_LeaderMatchIndexValid /\ UpdateTermAction => H_LeaderMatchIndexValid' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_LeaderMatchIndexValid,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_LeaderMatchIndexValid,BecomeLeaderAction)
  <1>3. TypeOK /\ H_LeaderMatchIndexValid /\ BecomeLeaderAction => H_LeaderMatchIndexValid' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_LeaderMatchIndexValid
  \* (H_LeaderMatchIndexValid,ClientRequestAction)
  <1>4. TypeOK /\ H_LeaderMatchIndexBound /\ H_LeaderMatchIndexValid /\ ClientRequestAction => H_LeaderMatchIndexValid' BY DEF TypeOK,H_LeaderMatchIndexBound,ClientRequestAction,ClientRequest,H_LeaderMatchIndexValid
  \* (H_LeaderMatchIndexValid,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_LeaderMatchIndexValid /\ AdvanceCommitIndexAction => H_LeaderMatchIndexValid' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_LeaderMatchIndexValid
  \* (H_LeaderMatchIndexValid,AppendEntriesAction)
  <1>6. TypeOK /\ H_LeaderMatchIndexValid /\ AppendEntriesAction => H_LeaderMatchIndexValid' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_LeaderMatchIndexValid
  \* (H_LeaderMatchIndexValid,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_LeaderMatchIndexValid /\ HandleRequestVoteRequestAction => H_LeaderMatchIndexValid' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_LeaderMatchIndexValid,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_LeaderMatchIndexValid,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_LeaderMatchIndexValid /\ HandleRequestVoteResponseAction => H_LeaderMatchIndexValid' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_LeaderMatchIndexValid,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_LeaderMatchIndexValid,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_LeaderMatchIndexValid /\ AcceptAppendEntriesRequestAppendAction => H_LeaderMatchIndexValid' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_LeaderMatchIndexValid
  \* (H_LeaderMatchIndexValid,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_LeaderMatchIndexValid /\ AcceptAppendEntriesRequestLearnCommitAction => H_LeaderMatchIndexValid' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_LeaderMatchIndexValid
  \* (H_LeaderMatchIndexValid,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_LeaderMatchIndexValidAppendEntries /\ H_LogMatching /\ H_LeaderMatchIndexValid /\ HandleAppendEntriesResponseAction => H_LeaderMatchIndexValid' BY DEF TypeOK,H_LeaderMatchIndexValidAppendEntries,H_LogMatching,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_LeaderMatchIndexValid
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_LogMatching
THEOREM L_36 == TypeOK /\ H_PrimaryHasEntriesItCreated /\ H_LogMatchingAppendEntries /\ H_LogMatching /\ Next => H_LogMatching'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_LogMatching,RequestVoteAction)
  <1>1. TypeOK /\ H_LogMatching /\ RequestVoteAction => H_LogMatching' BY DEF TypeOK,RequestVoteAction,RequestVote,H_LogMatching,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_LogMatching,UpdateTermAction)
  <1>2. TypeOK /\ H_LogMatching /\ UpdateTermAction => H_LogMatching' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_LogMatching,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_LogMatching,BecomeLeaderAction)
  <1>3. TypeOK /\ H_LogMatching /\ BecomeLeaderAction => H_LogMatching' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_LogMatching
  \* (H_LogMatching,ClientRequestAction)
  <1>4. TypeOK /\ H_PrimaryHasEntriesItCreated /\ H_LogMatching /\ ClientRequestAction => H_LogMatching' BY DEF TypeOK,H_PrimaryHasEntriesItCreated,ClientRequestAction,ClientRequest,H_LogMatching
  \* (H_LogMatching,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_LogMatching /\ AdvanceCommitIndexAction => H_LogMatching' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_LogMatching
  \* (H_LogMatching,AppendEntriesAction)
  <1>6. TypeOK /\ H_LogMatching /\ AppendEntriesAction => H_LogMatching' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_LogMatching
  \* (H_LogMatching,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_LogMatching /\ HandleRequestVoteRequestAction => H_LogMatching' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_LogMatching,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_LogMatching,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_LogMatching /\ HandleRequestVoteResponseAction => H_LogMatching' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_LogMatching,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_LogMatching,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_LogMatchingAppendEntries /\ H_LogMatching /\ AcceptAppendEntriesRequestAppendAction => H_LogMatching' BY DEF TypeOK,H_LogMatchingAppendEntries,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_LogMatching
  \* (H_LogMatching,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_LogMatching /\ AcceptAppendEntriesRequestLearnCommitAction => H_LogMatching' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_LogMatching
  \* (H_LogMatching,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_LogMatching /\ HandleAppendEntriesResponseAction => H_LogMatching' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_LogMatching
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** H_CommitIndexInAppendEntriesImpliesCommittedEntryExists
THEOREM L_37 == TypeOK /\ H_CommitIndexInAppendEntriesImpliesCommittedEntryExists /\ Next => H_CommitIndexInAppendEntriesImpliesCommittedEntryExists'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_CommitIndexInAppendEntriesImpliesCommittedEntryExists,RequestVoteAction)
  <1>1. TypeOK /\ H_CommitIndexInAppendEntriesImpliesCommittedEntryExists /\ RequestVoteAction => H_CommitIndexInAppendEntriesImpliesCommittedEntryExists' BY DEF TypeOK,RequestVoteAction,RequestVote,H_CommitIndexInAppendEntriesImpliesCommittedEntryExists,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_CommitIndexInAppendEntriesImpliesCommittedEntryExists,UpdateTermAction)
  <1>2. TypeOK /\ H_CommitIndexInAppendEntriesImpliesCommittedEntryExists /\ UpdateTermAction => H_CommitIndexInAppendEntriesImpliesCommittedEntryExists' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_CommitIndexInAppendEntriesImpliesCommittedEntryExists,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_CommitIndexInAppendEntriesImpliesCommittedEntryExists,BecomeLeaderAction)
  <1>3. TypeOK /\ H_CommitIndexInAppendEntriesImpliesCommittedEntryExists /\ BecomeLeaderAction => H_CommitIndexInAppendEntriesImpliesCommittedEntryExists' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_CommitIndexInAppendEntriesImpliesCommittedEntryExists
  \* (H_CommitIndexInAppendEntriesImpliesCommittedEntryExists,ClientRequestAction)
  <1>4. TypeOK /\ H_CommitIndexInAppendEntriesImpliesCommittedEntryExists /\ ClientRequestAction => H_CommitIndexInAppendEntriesImpliesCommittedEntryExists' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_CommitIndexInAppendEntriesImpliesCommittedEntryExists
  \* (H_CommitIndexInAppendEntriesImpliesCommittedEntryExists,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_CommitIndexInAppendEntriesImpliesCommittedEntryExists /\ AdvanceCommitIndexAction => H_CommitIndexInAppendEntriesImpliesCommittedEntryExists' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_CommitIndexInAppendEntriesImpliesCommittedEntryExists
  \* (H_CommitIndexInAppendEntriesImpliesCommittedEntryExists,AppendEntriesAction)
  <1>6. TypeOK /\ H_CommitIndexInAppendEntriesImpliesCommittedEntryExists /\ AppendEntriesAction => H_CommitIndexInAppendEntriesImpliesCommittedEntryExists' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_CommitIndexInAppendEntriesImpliesCommittedEntryExists
  \* (H_CommitIndexInAppendEntriesImpliesCommittedEntryExists,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_CommitIndexInAppendEntriesImpliesCommittedEntryExists /\ HandleRequestVoteRequestAction => H_CommitIndexInAppendEntriesImpliesCommittedEntryExists' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_CommitIndexInAppendEntriesImpliesCommittedEntryExists,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_CommitIndexInAppendEntriesImpliesCommittedEntryExists,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_CommitIndexInAppendEntriesImpliesCommittedEntryExists /\ HandleRequestVoteResponseAction => H_CommitIndexInAppendEntriesImpliesCommittedEntryExists' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_CommitIndexInAppendEntriesImpliesCommittedEntryExists,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_CommitIndexInAppendEntriesImpliesCommittedEntryExists,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_CommitIndexInAppendEntriesImpliesCommittedEntryExists /\ AcceptAppendEntriesRequestAppendAction => H_CommitIndexInAppendEntriesImpliesCommittedEntryExists' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_CommitIndexInAppendEntriesImpliesCommittedEntryExists
  \* (H_CommitIndexInAppendEntriesImpliesCommittedEntryExists,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_CommitIndexInAppendEntriesImpliesCommittedEntryExists /\ AcceptAppendEntriesRequestLearnCommitAction => H_CommitIndexInAppendEntriesImpliesCommittedEntryExists' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_CommitIndexInAppendEntriesImpliesCommittedEntryExists
  \* (H_CommitIndexInAppendEntriesImpliesCommittedEntryExists,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_CommitIndexInAppendEntriesImpliesCommittedEntryExists /\ HandleAppendEntriesResponseAction => H_CommitIndexInAppendEntriesImpliesCommittedEntryExists' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_CommitIndexInAppendEntriesImpliesCommittedEntryExists
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\* (ROOT SAFETY PROP)
\*** H_NoLogDivergence
THEOREM L_38 == TypeOK /\ H_CommitIndexBoundValid /\ H_LeaderMatchIndexValid /\ H_CommitIndexCoveredOnQuorum /\ H_LogMatching /\ H_CommitIndexBoundValid /\ H_CommitIndexInAppendEntriesImpliesCommittedEntryExists /\ H_LogMatching /\ H_NoLogDivergence /\ Next => H_NoLogDivergence'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_NoLogDivergence,RequestVoteAction)
  <1>1. TypeOK /\ H_NoLogDivergence /\ RequestVoteAction => H_NoLogDivergence' BY DEF TypeOK,RequestVoteAction,RequestVote,H_NoLogDivergence,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_NoLogDivergence,UpdateTermAction)
  <1>2. TypeOK /\ H_NoLogDivergence /\ UpdateTermAction => H_NoLogDivergence' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_NoLogDivergence,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (H_NoLogDivergence,BecomeLeaderAction)
  <1>3. TypeOK /\ H_NoLogDivergence /\ BecomeLeaderAction => H_NoLogDivergence' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_NoLogDivergence
  \* (H_NoLogDivergence,ClientRequestAction)
  <1>4. TypeOK /\ H_CommitIndexBoundValid /\ H_NoLogDivergence /\ ClientRequestAction => H_NoLogDivergence' BY DEF TypeOK,H_CommitIndexBoundValid,ClientRequestAction,ClientRequest,H_NoLogDivergence
  \* (H_NoLogDivergence,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_LeaderMatchIndexValid /\ H_CommitIndexCoveredOnQuorum /\ H_LogMatching /\ H_NoLogDivergence /\ AdvanceCommitIndexAction => H_NoLogDivergence' BY DEF TypeOK,H_LeaderMatchIndexValid,H_CommitIndexCoveredOnQuorum,H_LogMatching,AdvanceCommitIndexAction,AdvanceCommitIndex,H_NoLogDivergence
  \* (H_NoLogDivergence,AppendEntriesAction)
  <1>6. TypeOK /\ H_NoLogDivergence /\ AppendEntriesAction => H_NoLogDivergence' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_NoLogDivergence
  \* (H_NoLogDivergence,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_NoLogDivergence /\ HandleRequestVoteRequestAction => H_NoLogDivergence' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_NoLogDivergence,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_NoLogDivergence,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ H_NoLogDivergence /\ HandleRequestVoteResponseAction => H_NoLogDivergence' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_NoLogDivergence,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (H_NoLogDivergence,AcceptAppendEntriesRequestAppendAction)
  <1>9. TypeOK /\ H_CommitIndexBoundValid /\ H_NoLogDivergence /\ AcceptAppendEntriesRequestAppendAction => H_NoLogDivergence' BY DEF TypeOK,H_CommitIndexBoundValid,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_NoLogDivergence
  \* (H_NoLogDivergence,AcceptAppendEntriesRequestLearnCommitAction)
  <1>10. TypeOK /\ H_CommitIndexInAppendEntriesImpliesCommittedEntryExists /\ H_LogMatching /\ H_NoLogDivergence /\ AcceptAppendEntriesRequestLearnCommitAction => H_NoLogDivergence' BY DEF TypeOK,H_CommitIndexInAppendEntriesImpliesCommittedEntryExists,H_LogMatching,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_NoLogDivergence
  \* (H_NoLogDivergence,HandleAppendEntriesResponseAction)
  <1>11. TypeOK /\ H_NoLogDivergence /\ HandleAppendEntriesResponseAction => H_NoLogDivergence' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_NoLogDivergence
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0,A1,A2,A3,A4,A5,A6,A7
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => H_NoLogDivergence BY DEF Init, H_NoLogDivergence, IndGlobal
    <1>2. Init => H_CommitIndexInAppendEntriesImpliesCommittedEntryExists BY DEF Init, H_CommitIndexInAppendEntriesImpliesCommittedEntryExists, IndGlobal
    <1>3. Init => H_LogMatching BY DEF Init, H_LogMatching, IndGlobal
    <1>4. Init => H_LeaderMatchIndexValid BY DEF Init, H_LeaderMatchIndexValid, IndGlobal
    <1>5. Init => H_CommitIndexCoveredOnQuorum BY DEF Init, H_CommitIndexCoveredOnQuorum, IndGlobal
    <1>6. Init => H_CommitIndexBoundValid BY DEF Init, H_CommitIndexBoundValid, IndGlobal
    <1>7. Init => H_PrimaryHasEntriesItCreated BY DEF Init, H_PrimaryHasEntriesItCreated, IndGlobal
    <1>8. Init => H_LogMatchingAppendEntries BY DEF Init, H_LogMatchingAppendEntries, IndGlobal
    <1>9. Init => H_LeaderMatchIndexBound BY DEF Init, H_LeaderMatchIndexBound, IndGlobal
    <1>10. Init => H_LeaderMatchIndexValidAppendEntries BY DEF Init, H_LeaderMatchIndexValidAppendEntries, IndGlobal
    <1>11. Init => H_OnePrimaryPerTerm BY DEF Init, H_OnePrimaryPerTerm, IndGlobal
    <1>12. Init => H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm BY DEF Init, H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm, IndGlobal
    <1>13. Init => H_PrimaryHasEntriesItCreatedAppendEntries BY DEF Init, H_PrimaryHasEntriesItCreatedAppendEntries, IndGlobal
    <1>14. Init => H_LogMatchingInAppendEntriesMsgsLeaders BY DEF Init, H_LogMatchingInAppendEntriesMsgsLeaders, IndGlobal
    <1>15. Init => H_LogMatchingBetweenAppendEntriesMsgs BY DEF Init, H_LogMatchingBetweenAppendEntriesMsgs, IndGlobal
    <1>16. Init => H_AppendEntriesRequestLogEntriesMustBeInLeaderLog BY DEF Init, H_AppendEntriesRequestLogEntriesMustBeInLeaderLog, IndGlobal
    <1>17. Init => H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm BY DEF Init, H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm, IndGlobal
    <1>18. Init => H_CandidateWithVotesGrantedInTermImplyNoOtherLeader BY DEF Init, H_CandidateWithVotesGrantedInTermImplyNoOtherLeader, IndGlobal
    <1>19. Init => H_LogEntryInTermImpliesSafeAtTerm BY DEF Init, H_LogEntryInTermImpliesSafeAtTerm, IndGlobal
    <1>20. Init => H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm BY DEF Init, H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm, IndGlobal
    <1>21. Init => H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm BY DEF Init, H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm, IndGlobal
    <1>22. Init => H_LogEntryInTermImpliesSafeAtTermAppendEntries BY DEF Init, H_LogEntryInTermImpliesSafeAtTermAppendEntries, IndGlobal
    <1>23. Init => H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm BY DEF Init, H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm, IndGlobal
    <1>24. Init => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm BY DEF Init, H_VotesCantBeGrantedTwiceToCandidatesInSameTerm, IndGlobal
    <1>25. Init => H_LeaderHasVotesGrantedQuorum BY DEF Init, H_LeaderHasVotesGrantedQuorum, IndGlobal
    <1>26. Init => H_VoteGrantedImpliesVoteResponseMsgConsistent BY DEF Init, H_VoteGrantedImpliesVoteResponseMsgConsistent, IndGlobal
    <1>27. Init => H_VoteInGrantedImpliesVotedFor BY DEF Init, H_VoteInGrantedImpliesVotedFor, IndGlobal
    <1>28. Init => H_VoteGrantedImpliesNodeSafeAtTerm BY DEF Init, H_VoteGrantedImpliesNodeSafeAtTerm, IndGlobal
    <1>29. Init => H_CandidateInTermVotedForItself BY DEF Init, H_CandidateInTermVotedForItself, IndGlobal
    <1>30. Init => H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm BY DEF Init, H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm, IndGlobal
    <1>31. Init => H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm BY DEF Init, H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm, IndGlobal
    <1>32. Init => H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm BY DEF Init, H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm, IndGlobal
    <1>33. Init => H_AppendEntriesRequestInTermImpliesSafeAtTerms BY DEF Init, H_AppendEntriesRequestInTermImpliesSafeAtTerms, IndGlobal
    <1>34. Init => H_AppendEntriesResponseInTermImpliesSafeAtTerms BY DEF Init, H_AppendEntriesResponseInTermImpliesSafeAtTerms, IndGlobal
    <1>35. Init => H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm BY DEF Init, H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm, IndGlobal
    <1>36. Init => H_RequestVoteResponseTermsMatchSource BY DEF Init, H_RequestVoteResponseTermsMatchSource, IndGlobal
    <1>37. Init => H_RequestVoteResponseMsgsInTermUnique BY DEF Init, H_RequestVoteResponseMsgsInTermUnique, IndGlobal
    <1>38. Init => H_QuorumsSafeAtTerms BY DEF Init, H_QuorumsSafeAtTerms, IndGlobal
    <1>39. Init => H_RequestVoteRequestFromNodeImpliesSafeAtTerm BY DEF Init, H_RequestVoteRequestFromNodeImpliesSafeAtTerm, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14,<1>15,<1>16,<1>17,<1>18,<1>19,<1>20,<1>21,<1>22,<1>23,<1>24,<1>25,<1>26,<1>27,<1>28,<1>29,<1>30,<1>31,<1>32,<1>33,<1>34,<1>35,<1>36,<1>37,<1>38 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13,L_14,L_15,L_16,L_17,L_18,L_19,L_20,L_21,L_22,L_23,L_24,L_25,L_26,L_27,L_28,L_29,L_30,L_31,L_32,L_33,L_34,L_35,L_36,L_37,L_38 DEF Next, IndGlobal

====
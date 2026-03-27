---- MODULE AbstractRaft_IndProofs_nfm ----
EXTENDS AbstractRaft,TLAPS, FiniteSetTheorems


LEMMA QuorumsExistForNonEmptySets ==
ASSUME NEW S, IsFiniteSet(S), S # {}
PROVE Quorums(Server) # {}
PROOF BY FS_EmptySet, FS_CardinalityType

LEMMA QuorumsAreServerSubsets ==
ASSUME TypeOK, NEW s \in Server
PROVE Quorums(Server) \subseteq SUBSET Server
PROOF BY DEF TypeOK

\* LEMMA AddingToQuorumRemainsQuorum == \A Q \in Quorum : \A s \in Server : Q \in Quorum => Q \cup {s} \in Quorum

\* \* If the intersection of two server sets is empty, then they can't both be quorums.
LEMMA EmptyIntersectionImpliesNotBothQuorums == 
    \A s1 \in SUBSET Server :
    \A s2 \in SUBSET Server :
        (s1 \cap s2 = {}) => ~(s1 \in Quorums(Server) /\ s2 \in Quorums(Server))


LEMMA StaticQuorumsOverlap == \A Q1,Q2 \in Quorums(Server) : Q1 \cap Q2 # {}

\* Proof Graph Stats
\* ==================
\* seed: None
\* num proof graph nodes: 12
\* num proof obligations: 72

IndGlobal == 
  /\ TypeOK
  /\ H_StateMachineSafety
  /\ H_CommittedEntryIsOnQuorum
  /\ H_LaterLogsHaveEarlierCommitted
  /\ H_LeaderCompleteness
  /\ H_LogEntryImpliesSafeAtTerm
  /\ H_TermsMonotonic
  /\ H_UniformLogEntries
  /\ H_QuorumsSafeAtTerms
  /\ H_PrimaryTermGTELogTerm
  /\ H_LogMatching
  /\ H_PrimaryHasOwnEntries
  /\ H_OnePrimaryPerTerm


\* mean in-degree: 1.75
\* median in-degree: 1
\* max in-degree: 6
\* min in-degree: 0
\* mean variable slice size: 0

ASSUME A0 == IsFiniteSet(Server) /\ Cardinality(Server) > 1
ASSUME A1 == Nil \notin Server
ASSUME A2 == (Primary # Server)
ASSUME A3 == Server = Server
ASSUME A4 == Quorums(Server) \subseteq SUBSET Server /\ {} \notin Quorums(Server) /\ Quorums(Server) # {} /\ \A s \in Server : {s} \notin Quorums(Server)
ASSUME A5 == MaxLogLen \in Nat
ASSUME A6 == MaxTerm \in Nat /\ InitTerm \in Nat /\ Terms \subseteq Nat
ASSUME A7 == Primary # Secondary

\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (TypeOK,ClientRequestAction)
  <1>1. TypeOK /\ TypeOK /\ ClientRequestAction => TypeOK' BY DEF TypeOK,ClientRequestAction,ClientRequest,TypeOK
  \* (TypeOK,GetEntriesAction)
  <1>2. TypeOK /\ TypeOK /\ GetEntriesAction => TypeOK' BY DEF TypeOK,GetEntriesAction,GetEntries,TypeOK
  \* (TypeOK,RollbackEntriesAction)
  <1>3. TypeOK /\ TypeOK /\ RollbackEntriesAction => TypeOK' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,TypeOK
  \* (TypeOK,BecomeLeaderAction)
  <1>4. TypeOK /\ TypeOK /\ BecomeLeaderAction => TypeOK' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,TypeOK
  \* (TypeOK,CommitEntryAction)
  <1>5. TypeOK /\ TypeOK /\ CommitEntryAction => TypeOK' BY DEF TypeOK,CommitEntryAction,CommitEntry,TypeOK
  \* (TypeOK,UpdateTermsAction)
  <1>6. TypeOK /\ TypeOK /\ UpdateTermsAction => TypeOK' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,TypeOK
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_OnePrimaryPerTerm
THEOREM L_1 == TypeOK /\ H_QuorumsSafeAtTerms /\ H_OnePrimaryPerTerm /\ Next => H_OnePrimaryPerTerm'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7, StaticQuorumsOverlap, EmptyIntersectionImpliesNotBothQuorums, QuorumsAreServerSubsets, QuorumsExistForNonEmptySets
  \* (H_OnePrimaryPerTerm,ClientRequestAction)
  <1>1. TypeOK /\ H_OnePrimaryPerTerm /\ ClientRequestAction => H_OnePrimaryPerTerm' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_OnePrimaryPerTerm
  \* (H_OnePrimaryPerTerm,GetEntriesAction)
  <1>2. TypeOK /\ H_OnePrimaryPerTerm /\ GetEntriesAction => H_OnePrimaryPerTerm' BY DEF TypeOK,GetEntriesAction,GetEntries,H_OnePrimaryPerTerm
  \* (H_OnePrimaryPerTerm,RollbackEntriesAction)
  <1>3. TypeOK /\ H_OnePrimaryPerTerm /\ RollbackEntriesAction => H_OnePrimaryPerTerm' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_OnePrimaryPerTerm
  \* (H_OnePrimaryPerTerm,BecomeLeaderAction)
  <1>4. TypeOK /\ H_QuorumsSafeAtTerms /\ H_OnePrimaryPerTerm /\ BecomeLeaderAction => H_OnePrimaryPerTerm'
    \* Decompose: pick the electing server and its quorum.
    <2>. SUFFICES ASSUME TypeOK, H_QuorumsSafeAtTerms, H_OnePrimaryPerTerm,
                        NEW i \in Server, NEW Q \in Quorums(Server), BecomeLeader(i, Q)
         PROVE H_OnePrimaryPerTerm'
         BY DEF BecomeLeaderAction
    \* Pick two servers that are both Primary with the same term in the post-state.
    <2>. SUFFICES ASSUME NEW s1 \in Server, NEW t1 \in Server,
                        state'[s1] = Primary, state'[t1] = Primary, currentTerm'[s1] = currentTerm'[t1]
         PROVE s1 = t1
         BY DEF H_OnePrimaryPerTerm
    \* The new leader i becomes Primary; all other Q members become Secondary; others keep state.
    <2>1. state'[i] = Primary
          BY DEF BecomeLeader
    <2>2. \A v \in Q : v # i => state'[v] = Secondary
          BY DEF BecomeLeader
    <2>3. \A v \in Server : v \notin Q /\ v # i => state'[v] = state[v]
          BY DEF BecomeLeader
    <2>4. \A v \in Q : currentTerm'[v] = currentTerm[i] + 1
          BY DEF BecomeLeader, CanVoteForOplog, LastTerm
    <2>5. \A v \in Server : v \notin Q => currentTerm'[v] = currentTerm[v]
          BY DEF BecomeLeader
    \* s1 must be Primary' so s1 is either i or was already Primary and not in Q.
    \* Similarly for t1. If both are i, done. If one is i and other is old primary, show terms differ.
    \* Case A: s1 = i and t1 = i.
    <2>6. CASE s1 = i /\ t1 = i
          BY <2>6
    \* Case B: s1 = i and t1 # i (t1 is an old primary not in Q).
    <2>7. CASE s1 = i /\ t1 # i
      \* t1 must not be in Q (otherwise it would be Secondary).
      <3>1. t1 \notin Q
            BY <2>2, <2>7
      \* t1 kept its old state, so it was Primary before.
      <3>2. state[t1] = Primary
            BY <2>3, <3>1, <2>7
      \* By H_QuorumsSafeAtTerms, there exists a quorum Q2 for t1 where all members have term >= currentTerm[t1].
      <3>3. \E Q2 \in Quorums(Server) : \A n \in Q2 : currentTerm[n] >= currentTerm[t1]
            BY <3>2 DEF H_QuorumsSafeAtTerms
      \* Q and Q2 overlap.
      <3>4. PICK Q2 \in Quorums(Server) : \A n \in Q2 : currentTerm[n] >= currentTerm[t1]
            BY <3>3
      <3>5. Q \cap Q2 # {}
            BY <3>4
      <3>6. PICK w \in Q \cap Q2 : TRUE
            BY <3>5
      \* w is in Q, so currentTerm[w] < currentTerm[i] + 1 (from CanVoteForOplog).
      <3>7. currentTerm[w] < currentTerm[i] + 1
            BY <3>6 DEF BecomeLeader, CanVoteForOplog, LastTerm
      \* w is in Q2, so currentTerm[w] >= currentTerm[t1].
      <3>8. currentTerm[w] >= currentTerm[t1]
            BY <3>6, <3>4
      \* So currentTerm[t1] < currentTerm[i] + 1, meaning currentTerm[t1] <= currentTerm[i].
      \* But currentTerm'[s1] = currentTerm[i] + 1 and currentTerm'[t1] = currentTerm[t1].
      <3>9. currentTerm'[s1] = currentTerm[i] + 1
            BY <2>4, <2>7 DEF BecomeLeader
      <3>10. currentTerm'[t1] = currentTerm[t1]
            BY <2>5, <3>1
      \* currentTerm[t1] <= currentTerm[i] < currentTerm[i] + 1 = currentTerm'[s1].
      \* So currentTerm'[t1] # currentTerm'[s1], contradiction.
      <3>11. currentTerm[t1] =< currentTerm[i]
            BY <3>7, <3>8 DEF TypeOK, Terms
      <3>a. currentTerm[i] \in Nat /\ currentTerm[t1] \in Nat
        <4>1. currentTerm[i] \in Nat
          BY DEF TypeOK, Terms
        <4>2. currentTerm[t1] \in Nat
          BY DEF TypeOK, Terms
        <4>3. QED
          BY <4>1, <4>2
            
      <3>b. currentTerm[i] + 1 > currentTerm[t1]
            BY <3>11, <3>a
      <3>12. currentTerm'[s1] # currentTerm'[t1]
            BY <3>9, <3>10, <3>b, <3>a
      <3>. QED BY <3>12
    \* Case C: s1 # i and t1 = i (symmetric to Case B).
    <2>8. CASE s1 # i /\ t1 = i
      <3>1. s1 \notin Q
            BY <2>2, <2>8
      <3>2. state[s1] = Primary
            BY <2>3, <3>1, <2>8
      <3>3. \E Q2 \in Quorums(Server) : \A n \in Q2 : currentTerm[n] >= currentTerm[s1]
            BY <3>2 DEF H_QuorumsSafeAtTerms
      <3>4. PICK Q2 \in Quorums(Server) : \A n \in Q2 : currentTerm[n] >= currentTerm[s1]
            BY <3>3
      <3>5. Q \cap Q2 # {}
            BY <3>4
      <3>6. PICK w \in Q \cap Q2 : TRUE
            BY <3>5
      <3>7. currentTerm[w] < currentTerm[i] + 1
            BY <3>6 DEF BecomeLeader, CanVoteForOplog, LastTerm
      <3>8. currentTerm[w] >= currentTerm[s1]
            BY <3>6, <3>4
      <3>9. currentTerm'[t1] = currentTerm[i] + 1
            BY <2>4, <2>8 DEF BecomeLeader
      <3>10. currentTerm'[s1] = currentTerm[s1]
            BY <2>5, <3>1
      <3>11. currentTerm[s1] =< currentTerm[i]
            BY <3>7, <3>8 DEF TypeOK, Terms
      <3>a. currentTerm[i] \in Nat /\ currentTerm[s1] \in Nat
            BY DEF TypeOK, Terms
      <3>12. currentTerm'[s1] # currentTerm'[t1]
            BY <3>9, <3>10, <3>11, <3>a
      <3>. QED BY <3>12
    \* Case D: Neither s1 nor t1 is i. Both were already Primary with unchanged terms.
    <2>9. CASE s1 # i /\ t1 # i
      <3>1. s1 \notin Q
            BY <2>2, <2>9
      <3>2. t1 \notin Q
            BY <2>2, <2>9
      <3>3. state[s1] = Primary /\ state[t1] = Primary
            BY <2>3, <3>1, <3>2, <2>9
      <3>4. currentTerm'[s1] = currentTerm[s1] /\ currentTerm'[t1] = currentTerm[t1]
            BY <2>5, <3>1, <3>2
      <3>5. currentTerm[s1] = currentTerm[t1]
            BY <3>4
      <3>. QED BY <3>3, <3>5 DEF H_OnePrimaryPerTerm
    <2>. QED BY <2>6, <2>7, <2>8, <2>9
  \* (H_OnePrimaryPerTerm,CommitEntryAction)
  <1>5. TypeOK /\ H_OnePrimaryPerTerm /\ CommitEntryAction => H_OnePrimaryPerTerm' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_OnePrimaryPerTerm
  \* (H_OnePrimaryPerTerm,UpdateTermsAction)
  <1>6. TypeOK /\ H_OnePrimaryPerTerm /\ UpdateTermsAction => H_OnePrimaryPerTerm' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_OnePrimaryPerTerm
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_PrimaryHasOwnEntries
THEOREM L_2 == TypeOK /\ H_OnePrimaryPerTerm /\ H_LogEntryImpliesSafeAtTerm /\ H_PrimaryHasOwnEntries /\ Next => H_PrimaryHasOwnEntries'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_PrimaryHasOwnEntries,ClientRequestAction)
  <1>1. TypeOK /\ H_OnePrimaryPerTerm /\ H_PrimaryHasOwnEntries /\ ClientRequestAction => H_PrimaryHasOwnEntries' BY DEF TypeOK,H_OnePrimaryPerTerm,ClientRequestAction,ClientRequest,H_PrimaryHasOwnEntries
  \* (H_PrimaryHasOwnEntries,GetEntriesAction)
  <1>2. TypeOK /\ H_PrimaryHasOwnEntries /\ GetEntriesAction => H_PrimaryHasOwnEntries' BY DEF TypeOK,GetEntriesAction,GetEntries,H_PrimaryHasOwnEntries
  \* (H_PrimaryHasOwnEntries,RollbackEntriesAction)
  <1>3. TypeOK /\ H_PrimaryHasOwnEntries /\ RollbackEntriesAction => H_PrimaryHasOwnEntries' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_PrimaryHasOwnEntries
  \* (H_PrimaryHasOwnEntries,BecomeLeaderAction)
  <1>4. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ H_PrimaryHasOwnEntries /\ BecomeLeaderAction => H_PrimaryHasOwnEntries' BY DEF TypeOK,H_LogEntryImpliesSafeAtTerm,BecomeLeaderAction,BecomeLeader,H_PrimaryHasOwnEntries
  \* (H_PrimaryHasOwnEntries,CommitEntryAction)
  <1>5. TypeOK /\ H_PrimaryHasOwnEntries /\ CommitEntryAction => H_PrimaryHasOwnEntries' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_PrimaryHasOwnEntries
  \* (H_PrimaryHasOwnEntries,UpdateTermsAction)
  <1>6. TypeOK /\ H_PrimaryHasOwnEntries /\ UpdateTermsAction => H_PrimaryHasOwnEntries' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_PrimaryHasOwnEntries
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_LogMatching
THEOREM L_3 == TypeOK /\ H_PrimaryHasOwnEntries /\ H_LogMatching /\ Next => H_LogMatching'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_LogMatching,ClientRequestAction)
  <1>1. TypeOK /\ H_PrimaryHasOwnEntries /\ H_LogMatching /\ ClientRequestAction => H_LogMatching' BY DEF TypeOK,H_PrimaryHasOwnEntries,ClientRequestAction,ClientRequest,H_LogMatching
  \* (H_LogMatching,GetEntriesAction)
  <1>2. TypeOK /\ H_LogMatching /\ GetEntriesAction => H_LogMatching' BY DEF TypeOK,GetEntriesAction,GetEntries,H_LogMatching
  \* (H_LogMatching,RollbackEntriesAction)
  <1>3. TypeOK /\ H_LogMatching /\ RollbackEntriesAction => H_LogMatching' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_LogMatching
  \* (H_LogMatching,BecomeLeaderAction)
  <1>4. TypeOK /\ H_LogMatching /\ BecomeLeaderAction => H_LogMatching' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_LogMatching
  \* (H_LogMatching,CommitEntryAction)
  <1>5. TypeOK /\ H_LogMatching /\ CommitEntryAction => H_LogMatching' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_LogMatching
  \* (H_LogMatching,UpdateTermsAction)
  <1>6. TypeOK /\ H_LogMatching /\ UpdateTermsAction => H_LogMatching' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_LogMatching
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_PrimaryTermGTELogTerm
THEOREM L_4 == TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ H_PrimaryTermGTELogTerm /\ Next => H_PrimaryTermGTELogTerm'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_PrimaryTermGTELogTerm,ClientRequestAction)
  <1>1. TypeOK /\ H_PrimaryTermGTELogTerm /\ ClientRequestAction => H_PrimaryTermGTELogTerm' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_PrimaryTermGTELogTerm
  \* (H_PrimaryTermGTELogTerm,GetEntriesAction)
  <1>2. TypeOK /\ H_PrimaryTermGTELogTerm /\ GetEntriesAction => H_PrimaryTermGTELogTerm' BY DEF TypeOK,GetEntriesAction,GetEntries,H_PrimaryTermGTELogTerm
  \* (H_PrimaryTermGTELogTerm,RollbackEntriesAction)
  <1>3. TypeOK /\ H_PrimaryTermGTELogTerm /\ RollbackEntriesAction => H_PrimaryTermGTELogTerm' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_PrimaryTermGTELogTerm
  \* (H_PrimaryTermGTELogTerm,BecomeLeaderAction)
  <1>4. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ H_PrimaryTermGTELogTerm /\ BecomeLeaderAction => H_PrimaryTermGTELogTerm' BY DEF TypeOK,H_LogEntryImpliesSafeAtTerm,BecomeLeaderAction,BecomeLeader,H_PrimaryTermGTELogTerm
  \* (H_PrimaryTermGTELogTerm,CommitEntryAction)
  <1>5. TypeOK /\ H_PrimaryTermGTELogTerm /\ CommitEntryAction => H_PrimaryTermGTELogTerm' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_PrimaryTermGTELogTerm
  \* (H_PrimaryTermGTELogTerm,UpdateTermsAction)
  <1>6. TypeOK /\ H_PrimaryTermGTELogTerm /\ UpdateTermsAction => H_PrimaryTermGTELogTerm' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_PrimaryTermGTELogTerm
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_QuorumsSafeAtTerms
THEOREM L_5 == TypeOK /\ H_QuorumsSafeAtTerms /\ Next => H_QuorumsSafeAtTerms'
  <1>. USE A0,A1,A2,A3,A4,A5,A6, StaticQuorumsOverlap, EmptyIntersectionImpliesNotBothQuorums, QuorumsAreServerSubsets, QuorumsExistForNonEmptySets
  \* (H_QuorumsSafeAtTerms,ClientRequestAction)
  <1>1. TypeOK /\ H_QuorumsSafeAtTerms /\ ClientRequestAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_QuorumsSafeAtTerms
  \* (H_QuorumsSafeAtTerms,GetEntriesAction)
  <1>2. TypeOK /\ H_QuorumsSafeAtTerms /\ GetEntriesAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,GetEntriesAction,GetEntries,H_QuorumsSafeAtTerms
  \* (H_QuorumsSafeAtTerms,RollbackEntriesAction)
  <1>3. TypeOK /\ H_QuorumsSafeAtTerms /\ RollbackEntriesAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_QuorumsSafeAtTerms
  \* (H_QuorumsSafeAtTerms,BecomeLeaderAction)
  <1>4. TypeOK /\ H_QuorumsSafeAtTerms /\ BecomeLeaderAction => H_QuorumsSafeAtTerms' 
    <2> SUFFICES ASSUME TypeOK,
                        H_QuorumsSafeAtTerms,
                        TRUE,
                        NEW s \in Server,
                        NEW Q \in Quorums(Server),
                        BecomeLeader(s, Q),
                        NEW s_1 \in Server',
                        (state[s_1] = Primary)'
                 PROVE  (\E Q_1 \in Quorums(Server) : \A n \in Q_1 : currentTerm[n] >= currentTerm[s_1])'
      BY DEF BecomeLeaderAction, H_QuorumsSafeAtTerms
    <2> QED
      BY DEF LastTerm, CanVoteForOplog, UpdateTermsExpr, TypeOK,BecomeLeaderAction,BecomeLeader,H_QuorumsSafeAtTerms
  \* (H_QuorumsSafeAtTerms,CommitEntryAction)
  <1>5. TypeOK /\ H_QuorumsSafeAtTerms /\ CommitEntryAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_QuorumsSafeAtTerms
  \* (H_QuorumsSafeAtTerms,UpdateTermsAction)
  <1>6. TypeOK /\ H_QuorumsSafeAtTerms /\ UpdateTermsAction => H_QuorumsSafeAtTerms' 
    <2> SUFFICES ASSUME TypeOK,
                        H_QuorumsSafeAtTerms,
                        TRUE,
                        NEW s \in Server, NEW t \in Server,
                        UpdateTerms(s, t),
                        NEW s_1 \in Server',
                        (state[s_1] = Primary)'
                 PROVE  (\E Q \in Quorums(Server) : \A n \in Q : currentTerm[n] >= currentTerm[s_1])'
      BY DEF H_QuorumsSafeAtTerms, UpdateTermsAction
    <2> QED
      BY DEF UpdateTermsExpr,TypeOK,UpdateTermsAction,UpdateTerms,H_QuorumsSafeAtTerms
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_UniformLogEntries
THEOREM L_6 == TypeOK /\ H_PrimaryHasOwnEntries /\ H_LogMatching /\ H_UniformLogEntries /\ Next => H_UniformLogEntries'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_UniformLogEntries,ClientRequestAction)
  <1>1. TypeOK /\ H_PrimaryHasOwnEntries /\ H_UniformLogEntries /\ ClientRequestAction => H_UniformLogEntries' BY DEF TypeOK,H_PrimaryHasOwnEntries,ClientRequestAction,ClientRequest,H_UniformLogEntries
  \* (H_UniformLogEntries,GetEntriesAction)
  <1>2. TypeOK /\ H_LogMatching /\ H_UniformLogEntries /\ GetEntriesAction => H_UniformLogEntries' BY DEF TypeOK,H_LogMatching,GetEntriesAction,GetEntries,H_UniformLogEntries
  \* (H_UniformLogEntries,RollbackEntriesAction)
  <1>3. TypeOK /\ H_UniformLogEntries /\ RollbackEntriesAction => H_UniformLogEntries' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_UniformLogEntries
  \* (H_UniformLogEntries,BecomeLeaderAction)
  <1>4. TypeOK /\ H_UniformLogEntries /\ BecomeLeaderAction => H_UniformLogEntries' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_UniformLogEntries
  \* (H_UniformLogEntries,CommitEntryAction)
  <1>5. TypeOK /\ H_UniformLogEntries /\ CommitEntryAction => H_UniformLogEntries' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_UniformLogEntries
  \* (H_UniformLogEntries,UpdateTermsAction)
  <1>6. TypeOK /\ H_UniformLogEntries /\ UpdateTermsAction => H_UniformLogEntries' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_UniformLogEntries
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_TermsMonotonic
THEOREM L_7 == TypeOK /\ H_PrimaryTermGTELogTerm /\ H_TermsMonotonic /\ Next => H_TermsMonotonic'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_TermsMonotonic,ClientRequestAction)
  <1>1. TypeOK /\ H_PrimaryTermGTELogTerm /\ H_TermsMonotonic /\ ClientRequestAction => H_TermsMonotonic' BY DEF TypeOK,H_PrimaryTermGTELogTerm,ClientRequestAction,ClientRequest,H_TermsMonotonic
  \* (H_TermsMonotonic,GetEntriesAction)
  <1>2. TypeOK /\ H_TermsMonotonic /\ GetEntriesAction => H_TermsMonotonic' BY DEF TypeOK,GetEntriesAction,GetEntries,H_TermsMonotonic
  \* (H_TermsMonotonic,RollbackEntriesAction)
  <1>3. TypeOK /\ H_TermsMonotonic /\ RollbackEntriesAction => H_TermsMonotonic' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_TermsMonotonic
  \* (H_TermsMonotonic,BecomeLeaderAction)
  <1>4. TypeOK /\ H_TermsMonotonic /\ BecomeLeaderAction => H_TermsMonotonic' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_TermsMonotonic
  \* (H_TermsMonotonic,CommitEntryAction)
  <1>5. TypeOK /\ H_TermsMonotonic /\ CommitEntryAction => H_TermsMonotonic' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_TermsMonotonic
  \* (H_TermsMonotonic,UpdateTermsAction)
  <1>6. TypeOK /\ H_TermsMonotonic /\ UpdateTermsAction => H_TermsMonotonic' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_TermsMonotonic
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_LogEntryImpliesSafeAtTerm
THEOREM L_8 == TypeOK /\ H_QuorumsSafeAtTerms /\ H_LogEntryImpliesSafeAtTerm /\ Next => H_LogEntryImpliesSafeAtTerm'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_LogEntryImpliesSafeAtTerm,ClientRequestAction)
  <1>1. TypeOK /\ H_QuorumsSafeAtTerms /\ H_LogEntryImpliesSafeAtTerm /\ ClientRequestAction => H_LogEntryImpliesSafeAtTerm' BY DEF TypeOK,H_QuorumsSafeAtTerms,ClientRequestAction,ClientRequest,H_LogEntryImpliesSafeAtTerm
  \* (H_LogEntryImpliesSafeAtTerm,GetEntriesAction)
  <1>2. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ GetEntriesAction => H_LogEntryImpliesSafeAtTerm' BY DEF TypeOK,GetEntriesAction,GetEntries,H_LogEntryImpliesSafeAtTerm
  \* (H_LogEntryImpliesSafeAtTerm,RollbackEntriesAction)
  <1>3. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ RollbackEntriesAction => H_LogEntryImpliesSafeAtTerm' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_LogEntryImpliesSafeAtTerm
  \* (H_LogEntryImpliesSafeAtTerm,BecomeLeaderAction)
  <1>4. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ BecomeLeaderAction => H_LogEntryImpliesSafeAtTerm' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_LogEntryImpliesSafeAtTerm
  \* (H_LogEntryImpliesSafeAtTerm,CommitEntryAction)
  <1>5. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ CommitEntryAction => H_LogEntryImpliesSafeAtTerm' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_LogEntryImpliesSafeAtTerm
  \* (H_LogEntryImpliesSafeAtTerm,UpdateTermsAction)
  <1>6. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ UpdateTermsAction => H_LogEntryImpliesSafeAtTerm' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_LogEntryImpliesSafeAtTerm
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_LeaderCompleteness
THEOREM L_9 == TypeOK /\ H_TermsMonotonic /\ H_UniformLogEntries /\ H_CommittedEntryIsOnQuorum /\ H_LaterLogsHaveEarlierCommitted /\ H_TermsMonotonic /\ H_QuorumsSafeAtTerms /\ H_LeaderCompleteness /\ Next => H_LeaderCompleteness'
  <1>. USE A0,A1,A2,A3,A4,A5,A6 DEF ImmediatelyCommitted, InLog
  \* (H_LeaderCompleteness,ClientRequestAction)
  <1>1. TypeOK /\ H_LeaderCompleteness /\ ClientRequestAction => H_LeaderCompleteness' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_LeaderCompleteness
  \* (H_LeaderCompleteness,GetEntriesAction)
  <1>2. TypeOK /\ H_LeaderCompleteness /\ GetEntriesAction => H_LeaderCompleteness' BY DEF TypeOK,GetEntriesAction,GetEntries,H_LeaderCompleteness
  \* (H_LeaderCompleteness,RollbackEntriesAction)
  <1>3. TypeOK /\ H_LeaderCompleteness /\ RollbackEntriesAction => H_LeaderCompleteness' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_LeaderCompleteness
  \* (H_LeaderCompleteness,BecomeLeaderAction)
  <1>4. TypeOK /\ H_TermsMonotonic /\ H_UniformLogEntries /\ H_CommittedEntryIsOnQuorum /\ H_LaterLogsHaveEarlierCommitted /\ H_LeaderCompleteness /\ BecomeLeaderAction => H_LeaderCompleteness' BY DEF TypeOK,H_TermsMonotonic,H_UniformLogEntries,H_CommittedEntryIsOnQuorum,H_LaterLogsHaveEarlierCommitted,BecomeLeaderAction,BecomeLeader,H_LeaderCompleteness
  \* (H_LeaderCompleteness,CommitEntryAction)
  <1>5. TypeOK /\ H_TermsMonotonic /\ H_QuorumsSafeAtTerms /\ H_LeaderCompleteness /\ CommitEntryAction => H_LeaderCompleteness' BY DEF TypeOK,H_TermsMonotonic,H_QuorumsSafeAtTerms,CommitEntryAction,CommitEntry,H_LeaderCompleteness
  \* (H_LeaderCompleteness,UpdateTermsAction)
  <1>6. TypeOK /\ H_LeaderCompleteness /\ UpdateTermsAction => H_LeaderCompleteness' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_LeaderCompleteness
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_LaterLogsHaveEarlierCommitted
THEOREM L_10 == TypeOK /\ H_LeaderCompleteness /\ H_TermsMonotonic /\ H_UniformLogEntries /\ H_LogEntryImpliesSafeAtTerm /\ H_LaterLogsHaveEarlierCommitted /\ Next => H_LaterLogsHaveEarlierCommitted'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_LaterLogsHaveEarlierCommitted,ClientRequestAction)
  <1>1. TypeOK /\ H_LeaderCompleteness /\ H_LaterLogsHaveEarlierCommitted /\ ClientRequestAction => H_LaterLogsHaveEarlierCommitted' BY DEF TypeOK,H_LeaderCompleteness,ClientRequestAction,ClientRequest,H_LaterLogsHaveEarlierCommitted
  \* (H_LaterLogsHaveEarlierCommitted,GetEntriesAction)
  <1>2. TypeOK /\ H_TermsMonotonic /\ H_UniformLogEntries /\ H_LaterLogsHaveEarlierCommitted /\ GetEntriesAction => H_LaterLogsHaveEarlierCommitted' BY DEF TypeOK,H_TermsMonotonic,H_UniformLogEntries,GetEntriesAction,GetEntries,H_LaterLogsHaveEarlierCommitted
  \* (H_LaterLogsHaveEarlierCommitted,RollbackEntriesAction)
  <1>3. TypeOK /\ H_LaterLogsHaveEarlierCommitted /\ RollbackEntriesAction => H_LaterLogsHaveEarlierCommitted' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_LaterLogsHaveEarlierCommitted
  \* (H_LaterLogsHaveEarlierCommitted,BecomeLeaderAction)
  <1>4. TypeOK /\ H_LaterLogsHaveEarlierCommitted /\ BecomeLeaderAction => H_LaterLogsHaveEarlierCommitted' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_LaterLogsHaveEarlierCommitted
  \* (H_LaterLogsHaveEarlierCommitted,CommitEntryAction)
  <1>5. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ H_LaterLogsHaveEarlierCommitted /\ CommitEntryAction => H_LaterLogsHaveEarlierCommitted' BY DEF TypeOK,H_LogEntryImpliesSafeAtTerm,CommitEntryAction,CommitEntry,H_LaterLogsHaveEarlierCommitted
  \* (H_LaterLogsHaveEarlierCommitted,UpdateTermsAction)
  <1>6. TypeOK /\ H_LaterLogsHaveEarlierCommitted /\ UpdateTermsAction => H_LaterLogsHaveEarlierCommitted' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_LaterLogsHaveEarlierCommitted
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_CommittedEntryIsOnQuorum
THEOREM L_11 == TypeOK /\ H_LaterLogsHaveEarlierCommitted /\ H_CommittedEntryIsOnQuorum /\ Next => H_CommittedEntryIsOnQuorum'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_CommittedEntryIsOnQuorum,ClientRequestAction)
  <1>1. TypeOK /\ H_CommittedEntryIsOnQuorum /\ ClientRequestAction => H_CommittedEntryIsOnQuorum' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_CommittedEntryIsOnQuorum
  \* (H_CommittedEntryIsOnQuorum,GetEntriesAction)
  <1>2. TypeOK /\ H_CommittedEntryIsOnQuorum /\ GetEntriesAction => H_CommittedEntryIsOnQuorum' BY DEF TypeOK,GetEntriesAction,GetEntries,H_CommittedEntryIsOnQuorum
  \* (H_CommittedEntryIsOnQuorum,RollbackEntriesAction)
  <1>3. TypeOK /\ H_LaterLogsHaveEarlierCommitted /\ H_CommittedEntryIsOnQuorum /\ RollbackEntriesAction => H_CommittedEntryIsOnQuorum' BY DEF TypeOK,H_LaterLogsHaveEarlierCommitted,RollbackEntriesAction,RollbackEntries,H_CommittedEntryIsOnQuorum
  \* (H_CommittedEntryIsOnQuorum,BecomeLeaderAction)
  <1>4. TypeOK /\ H_CommittedEntryIsOnQuorum /\ BecomeLeaderAction => H_CommittedEntryIsOnQuorum' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_CommittedEntryIsOnQuorum
  \* (H_CommittedEntryIsOnQuorum,CommitEntryAction)
  <1>5. TypeOK /\ H_CommittedEntryIsOnQuorum /\ CommitEntryAction => H_CommittedEntryIsOnQuorum' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_CommittedEntryIsOnQuorum
  \* (H_CommittedEntryIsOnQuorum,UpdateTermsAction)
  <1>6. TypeOK /\ H_CommittedEntryIsOnQuorum /\ UpdateTermsAction => H_CommittedEntryIsOnQuorum' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_CommittedEntryIsOnQuorum
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\* (ROOT SAFETY PROP)
\*** H_StateMachineSafety
THEOREM L_12 == TypeOK /\ H_CommittedEntryIsOnQuorum /\ H_StateMachineSafety /\ Next => H_StateMachineSafety'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_StateMachineSafety,ClientRequestAction)
  <1>1. TypeOK /\ H_StateMachineSafety /\ ClientRequestAction => H_StateMachineSafety' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_StateMachineSafety
  \* (H_StateMachineSafety,GetEntriesAction)
  <1>2. TypeOK /\ H_StateMachineSafety /\ GetEntriesAction => H_StateMachineSafety' BY DEF TypeOK,GetEntriesAction,GetEntries,H_StateMachineSafety
  \* (H_StateMachineSafety,RollbackEntriesAction)
  <1>3. TypeOK /\ H_StateMachineSafety /\ RollbackEntriesAction => H_StateMachineSafety' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_StateMachineSafety
  \* (H_StateMachineSafety,BecomeLeaderAction)
  <1>4. TypeOK /\ H_StateMachineSafety /\ BecomeLeaderAction => H_StateMachineSafety' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_StateMachineSafety
  \* (H_StateMachineSafety,CommitEntryAction)
  <1>5. TypeOK /\ H_CommittedEntryIsOnQuorum /\ H_StateMachineSafety /\ CommitEntryAction => H_StateMachineSafety' BY DEF TypeOK,H_CommittedEntryIsOnQuorum,CommitEntryAction,CommitEntry,H_StateMachineSafety
  \* (H_StateMachineSafety,UpdateTermsAction)
  <1>6. TypeOK /\ H_StateMachineSafety /\ UpdateTermsAction => H_StateMachineSafety' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_StateMachineSafety
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0,A1,A2,A3,A4,A5,A6
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => H_OnePrimaryPerTerm BY DEF Init, H_OnePrimaryPerTerm, IndGlobal
    <1>2. Init => H_PrimaryHasOwnEntries BY DEF Init, H_PrimaryHasOwnEntries, IndGlobal
    <1>3. Init => H_LogMatching BY DEF Init, H_LogMatching, IndGlobal
    <1>4. Init => H_PrimaryTermGTELogTerm BY DEF Init, H_PrimaryTermGTELogTerm, IndGlobal
    <1>5. Init => H_QuorumsSafeAtTerms BY DEF Init, H_QuorumsSafeAtTerms, IndGlobal
    <1>6. Init => H_UniformLogEntries BY DEF Init, H_UniformLogEntries, IndGlobal
    <1>7. Init => H_TermsMonotonic BY DEF Init, H_TermsMonotonic, IndGlobal
    <1>8. Init => H_LogEntryImpliesSafeAtTerm BY DEF Init, H_LogEntryImpliesSafeAtTerm, IndGlobal
    <1>9. Init => H_LeaderCompleteness BY DEF Init, H_LeaderCompleteness, IndGlobal
    <1>10. Init => H_LaterLogsHaveEarlierCommitted BY DEF Init, H_LaterLogsHaveEarlierCommitted, IndGlobal
    <1>11. Init => H_CommittedEntryIsOnQuorum BY DEF Init, H_CommittedEntryIsOnQuorum, IndGlobal
    <1>12. Init => H_StateMachineSafety BY DEF Init, H_StateMachineSafety, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12 DEF Next, IndGlobal

====

====
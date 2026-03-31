---- MODULE AbstractRaft_IndProofs_nfm ----
EXTENDS AbstractRaft,TLAPS, FiniteSetTheorems, SequenceTheorems, WellFoundedInduction


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

\* Well-ordering of Nat: every non-empty subset has a minimum element.
\* Uses SmallestNatural from NaturalsInduction library.
LEMMA MinNatInSubset ==
  ASSUME NEW S, S \subseteq Nat, S # {}
  PROVE \E n \in S : \A m \in S : n <= m
PROOF
  <1>1. IsWellFoundedOn(OpToRel(<,Nat), Nat) BY NatLessThanWellFounded
  <1>2. \E x \in S : \A y \in S : ~(<<y,x>> \in OpToRel(<,Nat))
        BY <1>1, WFMin
  <1>3. PICK x \in S : \A y \in S : ~(<<y,x>> \in OpToRel(<,Nat)) BY <1>2
  <1>4. \A y \in S : ~(y < x) BY <1>3 DEF OpToRel
  <1>5. \A y \in S : x <= y BY <1>4
  <1>. QED BY <1>3, <1>5

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
ASSUME A6 == MaxTerm \in Nat /\ InitTerm \in Nat /\ Terms = Nat /\ LogIndices = Nat
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
  <1>4. TypeOK /\ TypeOK /\ BecomeLeaderAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ BecomeLeaderAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (currentTerm \in [Server -> Terms])'
      BY DEF CanVoteForOplog,TypeOK,BecomeLeaderAction,BecomeLeader,TypeOK
    <2>2. (state \in [Server -> {Secondary, Primary}])'
      BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,TypeOK
    <2>3. (log \in [Server -> Seq(Terms)])'
      BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,TypeOK
    <2>4. (immediatelyCommitted \in SUBSET (LogIndices \X Terms))'
      BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,TypeOK
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4 DEF TypeOK
  \* (TypeOK,CommitEntryAction)
  <1>5. TypeOK /\ TypeOK /\ CommitEntryAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ CommitEntryAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (currentTerm \in [Server -> Terms])'
      BY DEF TypeOK,CommitEntryAction,CommitEntry,TypeOK
    <2>2. (state \in [Server -> {Secondary, Primary}])'
      BY DEF TypeOK,CommitEntryAction,CommitEntry,TypeOK
    <2>3. (log \in [Server -> Seq(Terms)])'
      BY DEF TypeOK,CommitEntryAction,CommitEntry,TypeOK
    <2>4. (immediatelyCommitted \in SUBSET (LogIndices \X Terms))'
      BY DEF ImmediatelyCommitted, TypeOK,CommitEntryAction,CommitEntry,TypeOK
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4 DEF TypeOK
  \* (TypeOK,UpdateTermsAction)
  <1>6. TypeOK /\ TypeOK /\ UpdateTermsAction => TypeOK' BY DEF UpdateTermsExpr,TypeOK,UpdateTermsAction,UpdateTerms,TypeOK
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
  <1>6. TypeOK /\ H_OnePrimaryPerTerm /\ UpdateTermsAction => H_OnePrimaryPerTerm' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,UpdateTermsExpr,H_OnePrimaryPerTerm
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_PrimaryHasOwnEntries
THEOREM L_2 == TypeOK /\ H_OnePrimaryPerTerm /\ H_LogEntryImpliesSafeAtTerm /\ H_PrimaryHasOwnEntries /\ Next => H_PrimaryHasOwnEntries'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_PrimaryHasOwnEntries,ClientRequestAction)
  <1>1. TypeOK /\ H_OnePrimaryPerTerm /\ H_PrimaryHasOwnEntries /\ ClientRequestAction => H_PrimaryHasOwnEntries' BY DEF TypeOK,H_OnePrimaryPerTerm,ClientRequestAction,ClientRequest,H_PrimaryHasOwnEntries,InLog
  \* (H_PrimaryHasOwnEntries,GetEntriesAction)
  <1>2. TypeOK /\ H_PrimaryHasOwnEntries /\ GetEntriesAction => H_PrimaryHasOwnEntries' BY DEF TypeOK,GetEntriesAction,GetEntries,H_PrimaryHasOwnEntries,InLog,Empty
  \* (H_PrimaryHasOwnEntries,RollbackEntriesAction)
  <1>3. TypeOK /\ H_PrimaryHasOwnEntries /\ RollbackEntriesAction => H_PrimaryHasOwnEntries'
    <2>. SUFFICES ASSUME TypeOK, H_PrimaryHasOwnEntries,
                        NEW i \in Server, NEW j \in Server, RollbackEntries(i, j)
         PROVE H_PrimaryHasOwnEntries'
         BY DEF RollbackEntriesAction
    <2>1. state[i] = Secondary BY DEF RollbackEntries, CanRollback
    <2>2. UNCHANGED <<currentTerm, state>> BY DEF RollbackEntries
    <2>3. log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i])-1)] BY DEF RollbackEntries, CanRollback
    <2>4. \A p \in Server : state[p] = Primary => p # i BY <2>1, A7
    <2>5. \A p \in Server : state[p] = Primary => log'[p] = log[p] BY <2>3, <2>4
    <2>. QED BY <2>2, <2>3, <2>4, <2>5 DEF H_PrimaryHasOwnEntries, InLog, TypeOK
  \* (H_PrimaryHasOwnEntries,BecomeLeaderAction)
  <1>4. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ H_PrimaryHasOwnEntries /\ BecomeLeaderAction => H_PrimaryHasOwnEntries'
    <2>. SUFFICES ASSUME TypeOK, H_LogEntryImpliesSafeAtTerm, H_PrimaryHasOwnEntries,
                        NEW i \in Server, NEW Q \in Quorums(Server), BecomeLeader(i, Q)
         PROVE H_PrimaryHasOwnEntries'
         BY DEF BecomeLeaderAction
    <2>1. UNCHANGED <<log>> BY DEF BecomeLeader
    <2>2. \A v \in Q : currentTerm[v] < currentTerm[i] + 1 BY DEF BecomeLeader, CanVoteForOplog, LastTerm
    <2>3. \A v \in Q : currentTerm'[v] = currentTerm[i] + 1 BY DEF BecomeLeader, CanVoteForOplog, LastTerm
    <2>4. \A v \in Server : v \notin Q => currentTerm'[v] = currentTerm[v] BY DEF BecomeLeader
    <2>5. state'[i] = Primary BY DEF BecomeLeader
    <2>6. \A v \in Q : v # i => state'[v] = Secondary BY DEF BecomeLeader
    <2>7. \A v \in Server : v \notin Q /\ v # i => state'[v] = state[v] BY DEF BecomeLeader
    \* No log entry anywhere has term = newTerm = currentTerm[i] + 1.
    \* Proof: if such entry existed, H_LogEntryImpliesSafeAtTerm gives a quorum Q2 with all terms >= newTerm.
    \* But Q \cap Q2 # {}, and all Q members had currentTerm < newTerm. Contradiction.
    <2>8. \A s \in Server : \A k \in DOMAIN log[s] : log[s][k] # currentTerm[i] + 1
      <3>. SUFFICES ASSUME NEW s \in Server, NEW k \in DOMAIN log[s], log[s][k] = currentTerm[i] + 1
           PROVE FALSE OBVIOUS
      <3>1. \E Q2 \in Quorums(Server) : \A n \in Q2 : currentTerm[n] >= currentTerm[i] + 1
            BY DEF H_LogEntryImpliesSafeAtTerm
      <3>2. PICK Q2 \in Quorums(Server) : \A n \in Q2 : currentTerm[n] >= currentTerm[i] + 1
            BY <3>1
      <3>3. Q \cap Q2 # {} BY <3>2, StaticQuorumsOverlap
      <3>4. PICK w \in Q \cap Q2 : TRUE BY <3>3
      <3>5. currentTerm[w] >= currentTerm[i] + 1 BY <3>4, <3>2
      <3>6. currentTerm[w] < currentTerm[i] + 1 BY <3>4, <2>2
      <3>. QED BY <3>5, <3>6 DEF TypeOK, Terms
    \* The only new primary is i. For old primaries (not in Q, not i), their terms are unchanged
    \* and log is unchanged, so the invariant holds from the pre-state.
    \* For i: no entry has term newTerm, so the condition is vacuously true.
    <2>9. i \in Q BY DEF BecomeLeader
    \* Now prove H_PrimaryHasOwnEntries'. Consider any primary p' and any server q in the post-state.
    \* If p' = i: currentTerm'[i] = newTerm, and <2>8 says no entry has term newTerm, so vacuously true.
    \* If p' # i: p' \notin Q (otherwise Secondary), so state[p'] = Primary and currentTerm'[p'] = currentTerm[p'].
    \*   The pre-state H_PrimaryHasOwnEntries gives us what we need since log is unchanged.
    <2>. QED BY <2>1, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF H_PrimaryHasOwnEntries, InLog, TypeOK
  \* (H_PrimaryHasOwnEntries,CommitEntryAction)
  <1>5. TypeOK /\ H_PrimaryHasOwnEntries /\ CommitEntryAction => H_PrimaryHasOwnEntries' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_PrimaryHasOwnEntries,InLog,ImmediatelyCommitted
  \* (H_PrimaryHasOwnEntries,UpdateTermsAction)
  <1>6. TypeOK /\ H_PrimaryHasOwnEntries /\ UpdateTermsAction => H_PrimaryHasOwnEntries' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,UpdateTermsExpr,H_PrimaryHasOwnEntries,InLog
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_LogMatching
THEOREM L_3 == TypeOK /\ H_PrimaryHasOwnEntries /\ H_LogMatching /\ Next => H_LogMatching'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_LogMatching,ClientRequestAction)
  <1>1. TypeOK /\ H_PrimaryHasOwnEntries /\ H_LogMatching /\ ClientRequestAction => H_LogMatching' BY DEF TypeOK,H_PrimaryHasOwnEntries,ClientRequestAction,ClientRequest,H_LogMatching,InLog
  \* (H_LogMatching,GetEntriesAction)
  <1>2. TypeOK /\ H_LogMatching /\ GetEntriesAction => H_LogMatching'
    <2>. SUFFICES ASSUME TypeOK, H_LogMatching,
                        NEW gi \in Server, NEW gj \in Server, GetEntries(gi, gj)
         PROVE H_LogMatching'
         BY DEF GetEntriesAction
    <2>1. UNCHANGED <<currentTerm, state, immediatelyCommitted>> BY DEF GetEntries
    <2>2. state[gi] = Secondary BY DEF GetEntries
    <2>3. Len(log[gj]) > Len(log[gi]) BY DEF GetEntries
    <2>4. LET newEntryIndex == IF Empty(log[gi]) THEN 1 ELSE Len(log[gi]) + 1
          IN  /\ newEntryIndex \in DOMAIN log[gj]
              /\ log' = [log EXCEPT ![gi] = Append(log[gi], log[gj][newEntryIndex])]
          BY DEF GetEntries, Empty, TypeOK, Terms
    <2>5. \A s \in Server : s # gi => log'[s] = log[s] BY <2>4 DEF TypeOK, Empty
    <2>6. \A k \in DOMAIN log[gi] : log'[gi][k] = log[gi][k] BY <2>4 DEF TypeOK, Empty
    <2>7. DOMAIN log[gi] \subseteq DOMAIN log'[gi] BY <2>4 DEF TypeOK, Empty
    \* GetEntries logOk check: if log[gi] is non-empty, log[gj][Len(log[gi])] = log[gi][Len(log[gi])].
    <2>8. (Len(log[gi]) > 0) => log[gj][Len(log[gi])] = log[gi][Len(log[gi])]
          BY DEF GetEntries, Empty
    \* By H_LogMatching on (gi, gj) with matching last entry:
    \* SubSeq(log[gi], 1, Len(log[gi])) = SubSeq(log[gj], 1, Len(log[gi])).
    <2>a. (Len(log[gi]) > 0) => Len(log[gi]) \in DOMAIN log[gi] /\ Len(log[gi]) \in DOMAIN log[gj]
          BY <2>3 DEF TypeOK, Terms
    <2>9. (Len(log[gi]) > 0) => SubSeq(log[gi], 1, Len(log[gi])) = SubSeq(log[gj], 1, Len(log[gi]))
          BY <2>8, <2>a DEF H_LogMatching, TypeOK
    \* So log[gi] is a prefix of log[gj]. The new entry extends this prefix by one.
    \* log'[gi] = SubSeq(log[gj], 1, Len(log[gi])+1).
    \* H_LogMatching' follows because:
    \* For s # gi, t # gi: logs unchanged, pre-state.
    \* For s = gi (or t = gi): log'[gi] is a prefix of log[gj], so matching entries
    \*   imply prefix matching (via H_LogMatching on gj and the other server).
    \* Prove H_LogMatching': for all s, t, k, if log'[s][k] = log'[t][k] and k \in DOMAIN of both,
    \* then SubSeq(log'[s], 1, k) = SubSeq(log'[t], 1, k).
    \* log'[gi] = Append(log[gi], log[gj][newEntryIndex]).
    \* log'[gi] is a prefix of log[gj] (up to Len(log[gi])+1).
    \* For s # gi and t # gi: logs unchanged, H_LogMatching from pre-state.
    \* For s = gi or t = gi: log'[gi] is a prefix of log[gj], so if log'[gi][k] = log'[t][k],
    \* then log[gj][k] = log'[t][k] = log[t][k], and H_LogMatching on (gj, t, k) gives prefix match.
    \* log'[gi] is a prefix of log[gj]: for all k <= Len(log'[gi]), log'[gi][k] = log[gj][k].
    <2>b. \A k \in DOMAIN log'[gi] : log'[gi][k] = log[gj][k]
      <3>1. CASE Len(log[gi]) = 0
        \* log[gi] empty, newEntryIndex = 1, log'[gi] = <<log[gj][1]>>.
        BY <3>1, <2>4 DEF TypeOK, Empty, Terms
      <3>2. CASE Len(log[gi]) > 0
        \* For k <= Len(log[gi]): log'[gi][k] = log[gi][k] = log[gj][k] (from SubSeq equality <2>9).
        \* For k = Len(log[gi])+1: log'[gi][k] = log[gj][k] (from Append).
        BY <3>2, <2>4, <2>6, <2>9 DEF TypeOK, Empty, Terms
      <3>. QED BY <3>1, <3>2 DEF TypeOK
    \* Now prove H_LogMatching'.
    \* For s # gi and t # gi: logs unchanged, pre-state H_LogMatching applies.
    \* For s = gi (or t = gi): log'[gi][k] = log[gj][k] (<2>b), so matching with any t
    \*   reduces to H_LogMatching on (gj, t) or (t, gj) in the pre-state.
    \*   SubSeq(log'[gi], 1, k) = SubSeq(log[gj], 1, k) (both are prefixes of log[gj]).
    <2>c. \A k \in DOMAIN log'[gi] : k \in DOMAIN log[gj]
          BY <2>3, <2>4 DEF TypeOK, Empty, Terms
    \* Prove H_LogMatching' by expanding the definition and providing key facts.
    \* The approach: for s = gi cases, split on whether k is in old domain or is the new entry.
    \* When k is in old domain, use SubSeq(log'[gi], 1, k) = SubSeq(log[gi], 1, k) (no Append issues).
    \* When k is the new entry, use log'[gi][k] = log[gj][k] and H_LogMatching on (gj, t).
    <2>. QED BY <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>b, <2>c DEF H_LogMatching, GetEntries, Empty, TypeOK, Terms
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
  <1>1. TypeOK /\ H_PrimaryTermGTELogTerm /\ ClientRequestAction => H_PrimaryTermGTELogTerm' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_PrimaryTermGTELogTerm,Terms
  \* (H_PrimaryTermGTELogTerm,GetEntriesAction)
  <1>2. TypeOK /\ H_PrimaryTermGTELogTerm /\ GetEntriesAction => H_PrimaryTermGTELogTerm' BY A7 DEF TypeOK,GetEntriesAction,GetEntries,H_PrimaryTermGTELogTerm,Empty
  \* (H_PrimaryTermGTELogTerm,RollbackEntriesAction)
  <1>3. TypeOK /\ H_PrimaryTermGTELogTerm /\ RollbackEntriesAction => H_PrimaryTermGTELogTerm' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_PrimaryTermGTELogTerm
  \* (H_PrimaryTermGTELogTerm,BecomeLeaderAction)
  <1>4. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ H_PrimaryTermGTELogTerm /\ BecomeLeaderAction => H_PrimaryTermGTELogTerm'
    <2>. SUFFICES ASSUME TypeOK, H_LogEntryImpliesSafeAtTerm, H_PrimaryTermGTELogTerm,
                        NEW i \in Server, NEW Q \in Quorums(Server), BecomeLeader(i, Q)
         PROVE H_PrimaryTermGTELogTerm'
         BY DEF BecomeLeaderAction
    <2>1. UNCHANGED <<log>> BY DEF BecomeLeader
    <2>2. i \in Q BY DEF BecomeLeader
    <2>3. \A v \in Q : currentTerm[v] < currentTerm[i] + 1 BY DEF BecomeLeader, CanVoteForOplog, LastTerm
    <2>4. \A v \in Q : currentTerm'[v] = currentTerm[i] + 1 BY DEF BecomeLeader, CanVoteForOplog, LastTerm
    <2>5. \A v \in Server : v \notin Q => currentTerm'[v] = currentTerm[v] BY DEF BecomeLeader
    <2>6. state'[i] = Primary BY DEF BecomeLeader
    <2>7. \A v \in Q : v # i => state'[v] = Secondary BY DEF BecomeLeader
    <2>8. \A v \in Server : v \notin Q /\ v # i => state'[v] = state[v] BY DEF BecomeLeader
    \* Every log entry everywhere has term < newTerm (same argument as L_2 <1>4).
    <2>9. \A s \in Server : \A k \in DOMAIN log[s] : log[s][k] < currentTerm[i] + 1
      <3>. SUFFICES ASSUME NEW s \in Server, NEW k \in DOMAIN log[s]
           PROVE log[s][k] < currentTerm[i] + 1 OBVIOUS
      <3>1. \E Q2 \in Quorums(Server) : \A n \in Q2 : currentTerm[n] >= log[s][k]
            BY DEF H_LogEntryImpliesSafeAtTerm
      <3>2. PICK Q2 \in Quorums(Server) : \A n \in Q2 : currentTerm[n] >= log[s][k]
            BY <3>1
      <3>3. Q \cap Q2 # {} BY <3>2, StaticQuorumsOverlap
      <3>4. PICK w \in Q \cap Q2 : TRUE BY <3>3
      <3>5. currentTerm[w] >= log[s][k] BY <3>4, <3>2
      <3>6. currentTerm[w] < currentTerm[i] + 1 BY <3>4, <2>3
      <3>. QED BY <3>5, <3>6 DEF TypeOK, Terms
    \* For the new primary i: currentTerm'[i] = newTerm > all log entry terms.
    \* For old primaries (not in Q): currentTerm unchanged, log unchanged, use pre-state invariant.
    <2>. QED BY <2>1, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, A7 DEF H_PrimaryTermGTELogTerm, TypeOK, Terms
  \* (H_PrimaryTermGTELogTerm,CommitEntryAction)
  <1>5. TypeOK /\ H_PrimaryTermGTELogTerm /\ CommitEntryAction => H_PrimaryTermGTELogTerm' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_PrimaryTermGTELogTerm
  \* (H_PrimaryTermGTELogTerm,UpdateTermsAction)
  <1>6. TypeOK /\ H_PrimaryTermGTELogTerm /\ UpdateTermsAction => H_PrimaryTermGTELogTerm' BY A7 DEF TypeOK,UpdateTermsAction,UpdateTerms,UpdateTermsExpr,H_PrimaryTermGTELogTerm
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
    <2>1. s \in Q BY DEF BecomeLeader
    <2>2. \A v \in Q : currentTerm'[v] = currentTerm[s] + 1 BY DEF BecomeLeader, CanVoteForOplog, LastTerm
    <2>3. \A v \in Server : v \notin Q => currentTerm'[v] = currentTerm[v] BY DEF BecomeLeader
    <2>4. state'[s] = Primary BY DEF BecomeLeader
    <2>5. \A v \in Q : v # s => state'[v] = Secondary BY DEF BecomeLeader
    <2>6. \A v \in Server : v \notin Q /\ v # s => state'[v] = state[v] BY DEF BecomeLeader
    \* Case 1: s_1 = s (the new leader). Q witnesses the quorum: all Q members have currentTerm' = newTerm.
    <2>7. CASE s_1 = s
      BY <2>1, <2>2, <2>7 DEF TypeOK, Terms
    \* Case 2: s_1 # s. Then s_1 \notin Q (otherwise Secondary). s_1 was Primary before with unchanged term.
    <2>8. CASE s_1 # s
      \* s_1 is not in Q.
      <3>1. s_1 \notin Q BY <2>5, <2>8, A7
      \* s_1 was Primary before.
      <3>2. state[s_1] = Primary BY <2>6, <3>1, <2>8
      \* currentTerm'[s_1] = currentTerm[s_1].
      <3>3. currentTerm'[s_1] = currentTerm[s_1] BY <2>3, <3>1
      \* By H_QuorumsSafeAtTerms, there's a quorum Q2 with all terms >= currentTerm[s_1].
      <3>4. PICK Q2 \in Quorums(Server) : \A n \in Q2 : currentTerm[n] >= currentTerm[s_1]
            BY <3>2 DEF H_QuorumsSafeAtTerms
      \* In the post-state, Q2 members' terms only increased (Q members got newTerm, others unchanged).
      <3>5. Q2 \subseteq Server BY <3>4
      <3>6. \A v \in Q : currentTerm[v] < currentTerm[s] + 1 BY DEF BecomeLeader, CanVoteForOplog, LastTerm
      <3>a. currentTerm[s_1] \in Nat BY DEF TypeOK, Terms
      <3>b. \A n \in Q2 : currentTerm[n] \in Nat BY <3>5 DEF TypeOK, Terms
      <3>d. currentTerm[s] \in Nat BY DEF TypeOK, Terms
      <3>7. \A n \in Q2 : currentTerm'[n] >= currentTerm[n]
        <4>. SUFFICES ASSUME NEW n \in Q2 PROVE currentTerm'[n] >= currentTerm[n] OBVIOUS
        <4>1. n \in Server BY <3>5
        <4>2. CASE n \in Q
          <5>1. currentTerm'[n] = currentTerm[s] + 1 BY <4>2, <2>2
          <5>2. currentTerm[n] < currentTerm[s] + 1 BY <4>2, <3>6
          <5>3. currentTerm[n] \in Nat BY <3>b
          \* a < b => a =< b for integers.
          <5>. QED BY <5>1, <5>2, <5>3, <3>d
        <4>3. CASE n \notin Q
          BY <4>1, <4>3, <2>3, <3>b DEF TypeOK, Terms
        <4>. QED BY <4>2, <4>3
      <3>c. \A n \in Q2 : currentTerm'[n] \in Nat BY <3>5, <2>2, <2>3, <3>6 DEF TypeOK, Terms
      <3>8. \A n \in Q2 : currentTerm'[n] >= currentTerm'[s_1]
            BY <3>3, <3>4, <3>7, <3>a, <3>b, <3>c
      <3>. QED BY <3>4, <3>8
    <2> QED BY <2>7, <2>8
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
    \* t becomes Secondary, so s_1 # t. s_1's state and term are unchanged.
    <2>1. state'[t] = Secondary BY DEF UpdateTerms, UpdateTermsExpr, TypeOK
    <2>2. s_1 # t BY <2>1, A7
    <2>3. currentTerm'[s_1] = currentTerm[s_1] BY <2>2 DEF UpdateTerms, UpdateTermsExpr
    <2>4. state[s_1] = Primary BY <2>2 DEF UpdateTerms, UpdateTermsExpr
    \* Pre-state gives us a witnessing quorum.
    <2>5. PICK Q \in Quorums(Server) : \A n \in Q : currentTerm[n] >= currentTerm[s_1]
          BY <2>4 DEF H_QuorumsSafeAtTerms
    \* t's term only increased, all others unchanged. So all Q members' terms >= in post-state.
    <2>6. \A n \in Q : currentTerm'[n] >= currentTerm[n]
          BY <2>5 DEF UpdateTerms, UpdateTermsExpr, TypeOK, Terms
    <2>a. currentTerm[s_1] \in Nat BY DEF TypeOK, Terms
    <2>b. Q \subseteq Server BY <2>5
    <2>c. \A n \in Q : currentTerm[n] \in Nat BY <2>b DEF TypeOK, Terms
    <2>d. \A n \in Q : currentTerm'[n] \in Nat BY <2>b DEF UpdateTerms, UpdateTermsExpr, TypeOK, Terms
    <2>7. \A n \in Q : currentTerm'[n] >= currentTerm'[s_1]
          BY <2>3, <2>5, <2>6, <2>a, <2>c, <2>d
    <2>8. Q \in Quorums(Server) BY <2>5
    <2> QED BY <2>7, <2>8
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_UniformLogEntries
THEOREM L_6 == TypeOK /\ H_PrimaryHasOwnEntries /\ H_LogMatching /\ H_UniformLogEntries /\ Next => H_UniformLogEntries'
  <1>. USE A0,A1,A2,A3,A4,A5,A6, SubSeqProperties, LenProperties
  \* (H_UniformLogEntries,ClientRequestAction)
  <1>1. TypeOK /\ H_PrimaryHasOwnEntries /\ H_UniformLogEntries /\ ClientRequestAction => H_UniformLogEntries'
    <2>. SUFFICES ASSUME TypeOK, H_PrimaryHasOwnEntries, H_UniformLogEntries,
                        NEW cr \in Server, ClientRequest(cr)
         PROVE H_UniformLogEntries'
         BY DEF ClientRequestAction
    <2>1. state[cr] = Primary BY DEF ClientRequest
    <2>2. log' = [log EXCEPT ![cr] = Append(log[cr], currentTerm[cr])] BY DEF ClientRequest
    <2>3. UNCHANGED <<currentTerm, state>> BY DEF ClientRequest
    \* For servers s # cr and t # cr, logs unchanged, invariant from pre-state.
    \* For s = cr: the new entry is at index Len(log[cr])+1 with term currentTerm[cr].
    \* H_PrimaryHasOwnEntries ensures no other server t has an entry with term currentTerm[cr]
    \* that cr doesn't have. And in cr's new log, the new entry is the last one.
    \* For t = cr and s # cr: log[s] unchanged, log'[cr] extends log[cr], so any entry
    \* in log'[cr] at index < i (where i is in DOMAIN log[s]) was in log[cr] too.
    \* Pick arbitrary s, t, i for the post-state invariant.
    <2>. SUFFICES ASSUME NEW s \in Server, NEW t \in Server,
                        NEW ii \in DOMAIN log'[s],
                        \A jj \in DOMAIN log'[s] : jj < ii => log'[s][jj] # log'[s][ii]
         PROVE ~(\E k \in DOMAIN log'[t] : log'[t][k] = log'[s][ii] /\ k < ii)
         BY DEF H_UniformLogEntries
    \* Case 1: s # cr and t # cr. Both logs unchanged.
    <2>4. CASE s # cr /\ t # cr
      BY <2>2, <2>3, <2>4 DEF H_UniformLogEntries, TypeOK
    \* Case 2: s = cr and t # cr.
    <2>5. CASE s = cr /\ t # cr
      \* Subcase: ii is in the old log domain.
      <3>1. CASE ii \in DOMAIN log[cr]
        \* Prove that H_UniformLogEntries held for (cr, t, ii) in the pre-state, so it holds in post-state.
        <4>1. \A jj \in DOMAIN log[cr] : (jj < ii) => log[cr][jj] # log[cr][ii]
          <5>1. \A idx \in DOMAIN log[cr] : log'[cr][idx] = log[cr][idx]
                BY <2>2, <2>5 DEF TypeOK
          <5>2. DOMAIN log[cr] \subseteq DOMAIN log'[cr]
                BY <2>2, <2>5 DEF TypeOK
          <5>. QED BY <5>1, <5>2, <3>1, <2>5 DEF TypeOK, Terms
        <4>. QED BY <2>2, <2>3, <2>5, <3>1, <4>1 DEF H_UniformLogEntries, TypeOK, Terms
      \* Subcase: ii is the new entry (ii = Len(log[cr]) + 1).
      <3>2. CASE ii \notin DOMAIN log[cr]
        \* ii = Len(log[cr]) + 1 and log'[s][ii] = currentTerm[cr].
        \* The condition "\A jj < ii : log'[s][jj] # log'[s][ii]" means no earlier entry
        \* in cr's log has value currentTerm[cr].
        \* By H_PrimaryHasOwnEntries, if any server t has an entry with value currentTerm[cr],
        \* then cr also has it (via InLog). But cr has no such entry at any index < ii.
        \* So t can't have one either.
        \* ii = Len(log[cr]) + 1 and log'[cr][ii] = currentTerm[cr].
        <4>1. ii = Len(log[cr]) + 1 BY <2>2, <2>5, <3>2 DEF TypeOK, Terms
        <4>2. log'[cr][ii] = currentTerm[cr] BY <4>1, <2>2, <2>5 DEF TypeOK
        \* No earlier entry in cr's log has term currentTerm[cr] (from SUFFICES + <4>2).
        <4>3. \A jj \in DOMAIN log[cr] : log[cr][jj] # currentTerm[cr]
          <5>1. DOMAIN log[cr] \subseteq DOMAIN log'[cr] BY <2>2, <2>5 DEF TypeOK
          <5>2. \A idx \in DOMAIN log[cr] : log'[cr][idx] = log[cr][idx] BY <2>2, <2>5 DEF TypeOK
          <5>3. \A jj \in DOMAIN log[cr] : jj < ii BY <4>1 DEF TypeOK, Terms
          <5>. QED BY <4>2, <5>1, <5>2, <5>3, <2>5 DEF TypeOK
        \* By H_PrimaryHasOwnEntries: if log[t][k] = currentTerm[cr] for some t and k,
        \* then InLog(<<k, currentTerm[cr]>>, cr), i.e., log[cr][k] = currentTerm[cr].
        \* But <4>3 says no entry in log[cr] has term currentTerm[cr]. Contradiction.
        <4>4. ~(\E k \in DOMAIN log[t] : log[t][k] = currentTerm[cr] /\ k < ii)
              BY <2>1, <4>3, <2>5 DEF H_PrimaryHasOwnEntries, InLog, TypeOK
        \* log'[t] = log[t] since t # cr.
        <4>5. log'[t] = log[t] BY <2>2, <2>5 DEF TypeOK
        <4>. QED BY <4>2, <4>4, <4>5, <2>5
      <3>. QED BY <3>1, <3>2
    \* Case 3: s # cr and t = cr.
    <2>6. CASE s # cr /\ t = cr
      \* log[s] unchanged, log'[cr] = Append(log[cr], currentTerm[cr]).
      \* Entries in log'[cr] at index k <= Len(log[cr]) equal log[cr][k].
      \* Pre-state invariant gives the result for those indices.
      \* The new entry at Len(log[cr])+1: if k < ii and k = Len(log[cr])+1,
      \* then ii > Len(log[cr])+1 which can't happen since ii \in DOMAIN log[s] = DOMAIN log'[s].
      <3>1. \A k \in DOMAIN log[cr] : log'[cr][k] = log[cr][k] BY <2>2, <2>6 DEF TypeOK
      <3>2. log'[s] = log[s] BY <2>2, <2>6 DEF TypeOK
      <3>3. ii \in DOMAIN log[s] BY <3>2
      <3>4. log'[s][ii] = log[s][ii] BY <3>2
      \* No k in old domain of log[cr] satisfies the violation (by pre-state invariant).
      <3>5. \A jj \in DOMAIN log[s] : jj < ii => log[s][jj] # log[s][ii]
            BY <3>2, <3>3 DEF TypeOK
      <3>6. ~(\E k \in DOMAIN log[cr] : log[cr][k] = log[s][ii] /\ k < ii)
            BY <3>3, <3>5, <2>6 DEF H_UniformLogEntries
      \* For new entry at Len(log[cr])+1: if it's < ii, then log'[cr][Len(log[cr])+1] = currentTerm[cr].
      \* H_PrimaryHasOwnEntries says: if log[s][ii] = currentTerm[cr], then InLog(<<ii, currentTerm[cr]>>, cr),
      \* i.e., cr has an entry with that term at index ii. But then log[cr][ii] = currentTerm[cr] = log[s][ii],
      \* which means in the pre-state, there IS an entry at index ii in log[cr] with value log[s][ii].
      \* But <3>5 says no k in DOMAIN log[cr] has log[cr][k] = log[s][ii] AND k < ii.
      \* So in particular ii itself is the only place. That means jj=ii has log[cr][jj] = log[s][ii].
      \* Actually what we need: the new k = Len(log[cr])+1 has k >= ii because InLog means
      \* cr has an entry at index ii, hence Len(log[cr]) >= ii, so Len(log[cr])+1 > ii >= k won't be < ii.
      \* Wait: k = Len(log[cr])+1 < ii means Len(log[cr]) < ii - 1 < ii. But if log[s][ii] = currentTerm[cr]
      \* and H_PrimaryHasOwnEntries says cr has this entry (InLog), then Len(log[cr]) >= ii, contradiction.
      <3>7. ASSUME log[s][ii] = currentTerm[cr] PROVE Len(log[cr]) >= ii
            BY <2>1, <3>3, <3>7, <2>6 DEF H_PrimaryHasOwnEntries, InLog, TypeOK
      <3>. QED BY <2>2, <2>6, <3>1, <3>4, <3>6, <3>7 DEF TypeOK, Terms
    \* Case 4: s = cr and t = cr.
    <2>7. CASE s = cr /\ t = cr
      BY <2>2, <2>3, <2>7 DEF H_UniformLogEntries, TypeOK, Terms
    <2>. QED BY <2>4, <2>5, <2>6, <2>7
  \* (H_UniformLogEntries,GetEntriesAction)
  <1>2. TypeOK /\ H_LogMatching /\ H_UniformLogEntries /\ GetEntriesAction => H_UniformLogEntries'
    <2>. SUFFICES ASSUME TypeOK, H_LogMatching, H_UniformLogEntries,
                        NEW i \in Server, NEW j \in Server, GetEntries(i, j)
         PROVE H_UniformLogEntries'
         BY DEF GetEntriesAction
    <2>1. state[i] = Secondary BY DEF GetEntries
    <2>2. UNCHANGED <<currentTerm, state>> BY DEF GetEntries
    <2>3. Len(log[j]) > Len(log[i]) BY DEF GetEntries
    <2>4. LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE Len(log[i]) + 1
              newEntry      == log[j][newEntryIndex]
              newLog        == Append(log[i], newEntry)
          IN log' = [log EXCEPT ![i] = newLog]
          BY DEF GetEntries, Empty
    \* The new log[i] is log[i] extended with one entry copied from log[j].
    \* For s # i and t # i: logs unchanged, invariant holds from pre-state.
    \* For s = i or t = i: the new entry at Len(log[i])+1 matches log[j] at that index.
    \* H_LogMatching ensures prefix consistency, which preserves H_UniformLogEntries.
    <2>. SUFFICES ASSUME NEW s \in Server, NEW t \in Server,
                        NEW ii \in DOMAIN log'[s],
                        \A jj \in DOMAIN log'[s] : jj < ii => log'[s][jj] # log'[s][ii]
         PROVE ~(\E k \in DOMAIN log'[t] : log'[t][k] = log'[s][ii] /\ k < ii)
         BY DEF H_UniformLogEntries
    \* Case 1: s # i and t # i. Both logs unchanged.
    <2>5. CASE s # i /\ t # i
      BY <2>2, <2>4, <2>5 DEF H_UniformLogEntries, TypeOK, Empty
    \* Case 2: s = i and t # i.
    <2>6. CASE s = i /\ t # i
      <3>1. CASE ii \in DOMAIN log[i]
        <4>1. \A idx \in DOMAIN log[i] : log'[i][idx] = log[i][idx] BY <2>4, <2>6 DEF TypeOK, Empty
        <4>2. DOMAIN log[i] \subseteq DOMAIN log'[i] BY <2>4, <2>6 DEF TypeOK, Empty
        <4>3. \A jj \in DOMAIN log[i] : jj < ii => log[i][jj] # log[i][ii]
              BY <4>1, <4>2, <3>1, <2>6 DEF TypeOK, Terms
        <4>. QED BY <2>2, <2>4, <2>6, <3>1, <4>1, <4>3 DEF H_UniformLogEntries, TypeOK, Terms, Empty
      <3>2. CASE ii \notin DOMAIN log[i]
        \* ii = Len(log[i])+1, log'[i][ii] = log[j][ii].
        <4>1. log'[i][ii] = log[j][ii] BY <2>4, <2>6, <3>2 DEF TypeOK, Terms, Empty
        \* For jj < ii (jj in DOMAIN log[i]): log'[i][jj] = log[i][jj].
        <4>2. \A jj \in DOMAIN log[i] : log'[i][jj] = log[i][jj] BY <2>4, <2>6 DEF TypeOK, Empty
        \* log[i] is a prefix of log[j] (from GetEntries log consistency and H_LogMatching).
        \* So log[i][jj] = log[j][jj] for all jj in DOMAIN log[i].
        <4>3. \A jj \in DOMAIN log[i] : log[i][jj] = log[j][jj]
              BY <2>3, <2>4, <2>6 DEF GetEntries, H_LogMatching, Empty, TypeOK, Terms
        \* So log'[i][jj] = log[j][jj] for jj < ii.
        \* Combined with SUFFICES: \A jj < ii : log[j][jj] # log[j][ii].
        <4>a. DOMAIN log[i] \subseteq DOMAIN log'[i] BY <2>4, <2>6 DEF TypeOK, Empty
        <4>b. ii = Len(log[i]) + 1 BY <3>2, <2>6, <2>4 DEF TypeOK, Terms, Empty
        <4>c. \A jj \in DOMAIN log[i] : jj < ii BY <4>b DEF TypeOK
        <4>4. \A jj \in DOMAIN log[i] : log[j][jj] # log[j][ii]
              BY <4>1, <4>2, <4>3, <4>a, <4>c, <3>2, <2>6 DEF TypeOK, Terms
        <4>5. ii \in DOMAIN log[j] BY <4>b, <2>3 DEF TypeOK, Terms
        <4>6. \A jj \in DOMAIN log[j] : jj < ii => log[j][jj] # log[j][ii]
              BY <4>3, <4>4, <4>b DEF TypeOK, Terms
        \* By H_UniformLogEntries on (j, t, ii):
        <4>. QED BY <4>1, <4>5, <4>6, <2>2, <2>4, <2>6, <3>2 DEF H_UniformLogEntries, TypeOK, Terms, Empty
      <3>. QED BY <3>1, <3>2
    \* Case 3: s # i and t = i.
    <2>7. CASE s # i /\ t = i
      <3>1. \A k \in DOMAIN log[i] : log'[i][k] = log[i][k] BY <2>4, <2>7 DEF TypeOK, Empty
      <3>2. log'[s] = log[s] BY <2>4, <2>7 DEF TypeOK, Empty
      <3>3. ii \in DOMAIN log[s] BY <3>2
      <3>4. \A jj \in DOMAIN log[s] : jj < ii => log[s][jj] # log[s][ii]
            BY <3>2, <3>3 DEF TypeOK
      \* Pre-state invariant: no entry in log[i] matches log[s][ii] at index < ii.
      <3>5. ~(\E k \in DOMAIN log[i] : log[i][k] = log[s][ii] /\ k < ii)
            BY <3>3, <3>4, <2>7 DEF H_UniformLogEntries
      \* Also, no entry in log[j] matches log[s][ii] at index < ii.
      <3>6. ~(\E k \in DOMAIN log[j] : log[j][k] = log[s][ii] /\ k < ii)
            BY <3>3, <3>4, <2>7 DEF H_UniformLogEntries
      \* The new entry in log'[i] at position Len(log[i])+1.
      <3>7. Len(log[i]) + 1 \in DOMAIN log[j] BY <2>3 DEF TypeOK, Terms
      <3>8. log'[i][Len(log[i]) + 1] = log[j][Len(log[i]) + 1] BY <2>4, <2>7 DEF TypeOK, Terms, Empty
      <3>. QED BY <2>2, <2>4, <2>7, <3>1, <3>2, <3>5, <3>6, <3>7, <3>8 DEF TypeOK, Terms, Empty
    \* Case 4: s = i and t = i.
    <2>8. CASE s = i /\ t = i
      BY <2>2, <2>4, <2>8 DEF H_UniformLogEntries, TypeOK, Terms, Empty
    <2>. QED BY <2>5, <2>6, <2>7, <2>8
  \* (H_UniformLogEntries,RollbackEntriesAction)
  <1>3. TypeOK /\ H_UniformLogEntries /\ RollbackEntriesAction => H_UniformLogEntries'
    <2>. SUFFICES ASSUME TypeOK, H_UniformLogEntries,
                        NEW i \in Server, NEW j \in Server, RollbackEntries(i, j)
         PROVE H_UniformLogEntries'
         BY DEF RollbackEntriesAction
    <2>1. UNCHANGED <<currentTerm, state>> BY DEF RollbackEntries
    <2>2. log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i])-1)] BY DEF RollbackEntries, CanRollback
    \* Only log[i] changed, and it's a prefix of the old log[i].
    \* H_UniformLogEntries is preserved since truncation only removes entries,
    \* it can't create new violations.
    <2>3. \A s \in Server : s # i => log'[s] = log[s] BY <2>2 DEF TypeOK
    <2>4. \A k \in DOMAIN log'[i] : log'[i][k] = log[i][k] BY <2>2 DEF TypeOK, Terms, CanRollback, RollbackEntries
    <2>5. DOMAIN log'[i] \subseteq DOMAIN log[i] BY <2>2 DEF TypeOK, Terms
    \* Pick arbitrary s, t, ii for the post-state invariant.
    <2>. SUFFICES ASSUME NEW s \in Server, NEW t \in Server,
                        NEW ii \in DOMAIN log'[s],
                        \A jj \in DOMAIN log'[s] : jj < ii => log'[s][jj] # log'[s][ii]
         PROVE ~(\E k \in DOMAIN log'[t] : log'[t][k] = log'[s][ii] /\ k < ii)
         BY DEF H_UniformLogEntries
    <2>6. CASE s # i /\ t # i
      <3>1. log'[s] = log[s] /\ log'[t] = log[t] BY <2>3, <2>6
      <3>. QED BY <3>1, <2>6 DEF H_UniformLogEntries, TypeOK
    <2>7. CASE s = i /\ t # i
      <3>1. \A jj \in DOMAIN log'[s] : jj \in DOMAIN log[s] /\ log'[s][jj] = log[s][jj]
            BY <2>7 DEF RollbackEntries, CanRollback, TypeOK
      <3>2. \A jj \in DOMAIN log[s] : (jj < ii) => (jj \in DOMAIN log'[s] /\ log'[s][jj] = log[s][jj])
            BY <2>7 DEF RollbackEntries, CanRollback, TypeOK
      <3>3. (\A jj \in DOMAIN log[s] : (jj < ii) => log[s][jj] # log[s][ii])
            BY <3>1, <3>2
      <3>4. ii \in DOMAIN log[s] BY <3>1, <2>7
      <3>5. log'[t] = log[t] BY <2>3, <2>7
      <3>6. ~(\E k \in DOMAIN log[t] : log[t][k] = log[s][ii] /\ k < ii)
            BY <3>3, <3>4 DEF H_UniformLogEntries
      <3>. QED BY <3>1, <3>5, <3>6, <2>7
    <2>8. CASE s # i /\ t = i
      \* log[s] unchanged. log'[t] \subseteq log[t]. Pre-state invariant on log[s], log[i] applies,
      \* and entries in log'[i] at index < ii are in log[i].
      <3>1. log'[s] = log[s] BY <2>3, <2>8
      <3>2. ii \in DOMAIN log[s] BY <3>1
      <3>3. \A jj \in DOMAIN log[s] : jj < ii => log[s][jj] # log[s][ii]
            BY <3>1, <3>2 DEF TypeOK
      <3>4. ~(\E k \in DOMAIN log[i] : log[i][k] = log[s][ii] /\ k < ii)
            BY <3>2, <3>3 DEF H_UniformLogEntries
      <3>5. \A k \in DOMAIN log'[i] : k \in DOMAIN log[i] /\ log'[i][k] = log[i][k]
            BY <2>8 DEF RollbackEntries, CanRollback, TypeOK
      <3>. QED BY <3>1, <3>4, <3>5, <2>8
    <2>9. CASE s = i /\ t = i
      <3>1. \A jj \in DOMAIN log'[s] : jj \in DOMAIN log[s] /\ log'[s][jj] = log[s][jj]
            BY <2>9 DEF RollbackEntries, CanRollback, TypeOK
      <3>2. \A jj \in DOMAIN log[s] : (jj < ii) => (jj \in DOMAIN log'[s] /\ log'[s][jj] = log[s][jj])
            BY <2>9 DEF RollbackEntries, CanRollback, TypeOK
      <3>3. \A jj \in DOMAIN log[s] : (jj < ii) => log[s][jj] # log[s][ii]
            BY <3>1, <3>2
      <3>4. ii \in DOMAIN log[s] BY <3>1, <2>9
      <3>5. ~(\E k \in DOMAIN log[s] : log[s][k] = log[s][ii] /\ k < ii)
            BY <3>4, <3>3 DEF H_UniformLogEntries
      <3>. QED BY <3>1, <3>5, <2>9
    <2>. QED BY <2>6, <2>7, <2>8, <2>9
  \* (H_UniformLogEntries,BecomeLeaderAction)
  <1>4. TypeOK /\ H_UniformLogEntries /\ BecomeLeaderAction => H_UniformLogEntries' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_UniformLogEntries
  \* (H_UniformLogEntries,CommitEntryAction)
  <1>5. TypeOK /\ H_UniformLogEntries /\ CommitEntryAction => H_UniformLogEntries' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_UniformLogEntries
  \* (H_UniformLogEntries,UpdateTermsAction)
  <1>6. TypeOK /\ H_UniformLogEntries /\ UpdateTermsAction => H_UniformLogEntries' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_UniformLogEntries
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_TermsMonotonic
THEOREM L_7 == TypeOK /\ H_PrimaryTermGTELogTerm /\ H_TermsMonotonic /\ Next => H_TermsMonotonic'
  <1>. USE A0,A1,A2,A3,A4,A5,A6 DEF CanRollback, LastTerm, LogTerm
  \* (H_TermsMonotonic,ClientRequestAction)
  <1>1. TypeOK /\ H_PrimaryTermGTELogTerm /\ H_TermsMonotonic /\ ClientRequestAction => H_TermsMonotonic' BY DEF TypeOK,H_PrimaryTermGTELogTerm,ClientRequestAction,ClientRequest,H_TermsMonotonic,Terms
  \* (H_TermsMonotonic,GetEntriesAction)
  <1>2. TypeOK /\ H_TermsMonotonic /\ GetEntriesAction => H_TermsMonotonic'
    <2>. SUFFICES ASSUME TypeOK, H_TermsMonotonic,
                        NEW gi \in Server, NEW gj \in Server, GetEntries(gi, gj)
         PROVE H_TermsMonotonic'
         BY DEF GetEntriesAction
    <2>1. UNCHANGED <<currentTerm, state>> BY DEF GetEntries
    <2>2. Len(log[gj]) > Len(log[gi]) BY DEF GetEntries
    \* The new last index of log'[gi].
    <2>3. LET sLastIdx == Len(log'[gi])
          IN  sLastIdx > 1 =>
              /\ log'[gi][sLastIdx] = log[gj][sLastIdx]
              /\ log[gj][sLastIdx] >= log[gj][sLastIdx - 1]
              /\ log[gj][sLastIdx - 1] = log[gi][sLastIdx - 1]
              /\ log'[gi][sLastIdx - 1] = log[gi][sLastIdx - 1]
          BY DEF GetEntries, Empty, H_TermsMonotonic, TypeOK, Terms
    \* For servers s # gi: log unchanged, pre-state monotonicity holds.
    \* For gi: all old entries preserved, and the new last entry >= previous by <2>3.
    <2>. QED BY <2>1, <2>2, <2>3 DEF GetEntries, Empty, H_TermsMonotonic, TypeOK, Terms
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
  <1>1. TypeOK /\ H_QuorumsSafeAtTerms /\ H_LogEntryImpliesSafeAtTerm /\ ClientRequestAction => H_LogEntryImpliesSafeAtTerm' BY DEF TypeOK,H_QuorumsSafeAtTerms,ClientRequestAction,ClientRequest,H_LogEntryImpliesSafeAtTerm,Terms
  \* (H_LogEntryImpliesSafeAtTerm,GetEntriesAction)
  <1>2. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ GetEntriesAction => H_LogEntryImpliesSafeAtTerm'
    <2>. SUFFICES ASSUME TypeOK, H_LogEntryImpliesSafeAtTerm,
                        NEW i \in Server, NEW j \in Server, GetEntries(i, j)
         PROVE H_LogEntryImpliesSafeAtTerm'
         BY DEF GetEntriesAction
    <2>1. UNCHANGED <<currentTerm, state>> BY DEF GetEntries
    <2>2. LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE Len(log[i]) + 1
          IN  /\ newEntryIndex \in DOMAIN log[j]
              /\ log' = [log EXCEPT ![i] = Append(log[i], log[j][newEntryIndex])]
          BY DEF GetEntries, Empty, TypeOK, Terms
    \* For any server s and index k in DOMAIN log'[s]:
    \* If s # i: log'[s] = log[s], use pre-state invariant with unchanged currentTerm.
    \* If s = i and k in DOMAIN log[i]: log'[i][k] = log[i][k], use pre-state on i.
    \* If s = i and k = newEntryIndex: log'[i][k] = log[j][newEntryIndex], use pre-state on j.
    <2>3. \A s \in Server : s # i => log'[s] = log[s] BY <2>2 DEF TypeOK, Empty
    <2>4. \A k \in DOMAIN log[i] : log'[i][k] = log[i][k] BY <2>2 DEF TypeOK, Empty
    <2>5. DOMAIN log[i] \subseteq DOMAIN log'[i] BY <2>2 DEF TypeOK, Empty
    \* The new entry in log'[i] (at newEntryIndex) equals log[j][newEntryIndex],
    \* which has a quorum by H_LogEntryImpliesSafeAtTerm on j.
    <2>6. LET idx == IF Empty(log[i]) THEN 1 ELSE Len(log[i]) + 1
          IN  \E Q \in Quorums(Server) : \A n \in Q : currentTerm[n] >= log[j][idx]
          BY <2>2 DEF H_LogEntryImpliesSafeAtTerm, TypeOK, Terms, Empty
    \* For s # i: log unchanged, currentTerm unchanged, pre-state applies.
    \* For s = i, k in old domain: log'[i][k] = log[i][k], pre-state on i applies.
    \* For s = i, k = newEntryIndex: <2>6 gives the quorum.
    <2>. SUFFICES ASSUME NEW s \in Server, NEW k \in DOMAIN log'[s]
         PROVE \E Q \in Quorums(Server) : \A n \in Q : currentTerm'[n] >= log'[s][k]
         BY <2>1 DEF H_LogEntryImpliesSafeAtTerm
    <2>7. CASE s # i
      BY <2>1, <2>3, <2>7 DEF H_LogEntryImpliesSafeAtTerm, TypeOK
    <2>8. CASE s = i /\ k \in DOMAIN log[i]
      BY <2>1, <2>4, <2>8 DEF H_LogEntryImpliesSafeAtTerm, TypeOK
    <2>9. CASE s = i /\ k \notin DOMAIN log[i]
      BY <2>1, <2>2, <2>6, <2>9 DEF H_LogEntryImpliesSafeAtTerm, Empty, TypeOK, Terms
    <2>. QED BY <2>7, <2>8, <2>9
  \* (H_LogEntryImpliesSafeAtTerm,RollbackEntriesAction)
  <1>3. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ RollbackEntriesAction => H_LogEntryImpliesSafeAtTerm' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_LogEntryImpliesSafeAtTerm
  \* (H_LogEntryImpliesSafeAtTerm,BecomeLeaderAction)
  <1>4. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ BecomeLeaderAction => H_LogEntryImpliesSafeAtTerm' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_LogEntryImpliesSafeAtTerm,CanVoteForOplog,LastTerm,Terms
  \* (H_LogEntryImpliesSafeAtTerm,CommitEntryAction)
  <1>5. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ CommitEntryAction => H_LogEntryImpliesSafeAtTerm' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_LogEntryImpliesSafeAtTerm
  \* (H_LogEntryImpliesSafeAtTerm,UpdateTermsAction)
  <1>6. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ UpdateTermsAction => H_LogEntryImpliesSafeAtTerm' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,UpdateTermsExpr,H_LogEntryImpliesSafeAtTerm,Terms
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_LeaderCompleteness
THEOREM L_9 == TypeOK /\ H_TermsMonotonic /\ H_UniformLogEntries /\ H_CommittedEntryIsOnQuorum /\ H_LaterLogsHaveEarlierCommitted /\ H_TermsMonotonic /\ H_QuorumsSafeAtTerms /\ H_LeaderCompleteness /\ Next => H_LeaderCompleteness'
  <1>. USE A0,A1,A2,A3,A4,A5,A6 DEF ImmediatelyCommitted, InLog
  \* (H_LeaderCompleteness,ClientRequestAction)
  <1>1. TypeOK /\ H_LeaderCompleteness /\ ClientRequestAction => H_LeaderCompleteness' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_LeaderCompleteness
  \* (H_LeaderCompleteness,GetEntriesAction)
  <1>2. TypeOK /\ H_LeaderCompleteness /\ GetEntriesAction => H_LeaderCompleteness' BY DEF TypeOK,GetEntriesAction,GetEntries,H_LeaderCompleteness
  \* (H_LeaderCompleteness,RollbackEntriesAction)
  <1>3. TypeOK /\ H_LeaderCompleteness /\ RollbackEntriesAction => H_LeaderCompleteness'
    <2>. SUFFICES ASSUME TypeOK, H_LeaderCompleteness,
                        NEW i \in Server, NEW j \in Server, RollbackEntries(i, j)
         PROVE H_LeaderCompleteness'
         BY DEF RollbackEntriesAction
    <2>1. state[i] = Secondary BY DEF RollbackEntries, CanRollback
    <2>2. UNCHANGED <<currentTerm, state, immediatelyCommitted>> BY DEF RollbackEntries
    <2>3. \A p \in Server : state[p] = Primary => p # i BY <2>1, A7
    <2>4. \A p \in Server : state[p] = Primary => log'[p] = log[p]
          BY <2>3 DEF RollbackEntries, CanRollback
    <2>. QED BY <2>2, <2>4 DEF H_LeaderCompleteness, TypeOK
  \* (H_LeaderCompleteness,BecomeLeaderAction)
  <1>4. TypeOK /\ H_TermsMonotonic /\ H_UniformLogEntries /\ H_CommittedEntryIsOnQuorum /\ H_LaterLogsHaveEarlierCommitted /\ H_LeaderCompleteness /\ BecomeLeaderAction => H_LeaderCompleteness'
    <2>. SUFFICES ASSUME TypeOK, H_TermsMonotonic, H_UniformLogEntries, H_CommittedEntryIsOnQuorum,
                        H_LaterLogsHaveEarlierCommitted, H_LeaderCompleteness,
                        NEW i \in Server, NEW Q \in Quorums(Server), BecomeLeader(i, Q)
         PROVE H_LeaderCompleteness'
         BY DEF BecomeLeaderAction
    \* Basic facts about BecomeLeader.
    <2>1. UNCHANGED <<log, immediatelyCommitted>> BY DEF BecomeLeader
    <2>2. i \in Q BY DEF BecomeLeader
    <2>3. \A v \in Q : CanVoteForOplog(v, i, currentTerm[i] + 1) BY DEF BecomeLeader
    <2>4. currentTerm' = [s \in Server |-> IF s \in Q THEN currentTerm[i] + 1 ELSE currentTerm[s]]
          BY DEF BecomeLeader
    <2>5. state' = [s \in Server |-> IF s = i THEN Primary
                                     ELSE IF s \in Q THEN Secondary
                                     ELSE state[s]]
          BY DEF BecomeLeader
    \* Q members other than i become Secondary, so vacuously satisfy H_LeaderCompleteness.
    <2>6. \A s \in Q : s # i => state'[s] = Secondary
          BY <2>5 DEF TypeOK
    \* Non-Q servers: state and currentTerm unchanged, use pre-state H_LeaderCompleteness.
    <2>7. \A s \in Server : s \notin Q /\ state'[s] = Primary =>
            \A c \in immediatelyCommitted : c[2] < currentTerm'[s] => InLog(<<c[1],c[2]>>, s)
          BY <2>1, <2>2, <2>4, <2>5 DEF H_LeaderCompleteness, InLog, TypeOK
    \* The hard case: i is the new primary. Must show all committed entries with term < newTerm are in log[i].
    <2>8. \A c \in immediatelyCommitted : c[2] < currentTerm[i] + 1 => InLog(<<c[1],c[2]>>, i)
      <3>. SUFFICES ASSUME NEW c \in immediatelyCommitted, c[2] < currentTerm[i] + 1
           PROVE InLog(<<c[1],c[2]>>, i)
           OBVIOUS
      \* By H_CommittedEntryIsOnQuorum, some quorum has c on all members.
      <3>1. PICK Q2 \in Quorums(Server) : \A n \in Q2 : InLog(<<c[1],c[2]>>, n)
            BY DEF H_CommittedEntryIsOnQuorum
      \* Vote quorum Q and commit quorum Q2 overlap.
      <3>2. Q \cap Q2 # {} BY StaticQuorumsOverlap
      <3>3. PICK w \in Q \cap Q2 : TRUE BY <3>2
      \* w has c in its log and voted for i.
      <3>4. InLog(<<c[1],c[2]>>, w) BY <3>3, <3>1
      <3>5. CanVoteForOplog(w, i, currentTerm[i] + 1) BY <3>3, <2>3
      \* Case 1: i has a log entry with term > c[2]. Use H_LaterLogsHaveEarlierCommitted.
      <3>6. CASE \E idx \in DOMAIN log[i] : log[i][idx] > c[2]
        <4>1. Len(log[i]) >= c[1] /\ log[i][c[1]] = c[2]
              BY <3>6 DEF H_LaterLogsHaveEarlierCommitted
        <4>2. c[1] \in DOMAIN log[i]
              BY <4>1 DEF TypeOK, LogIndices, Terms
        <4>. QED BY <4>1, <4>2 DEF InLog
      \* Case 2: all entries in i's log have term <= c[2].
      <3>7. CASE ~\E idx \in DOMAIN log[i] : log[i][idx] > c[2]
        \* w has c in its log: log[w][c[1]] = c[2], c[1] in DOMAIN log[w].
        <4>1. log[w][c[1]] = c[2] /\ c[1] \in DOMAIN log[w]
              BY <3>4 DEF InLog, TypeOK
        \* i's log is at least as up-to-date as w's.
        <4>2. \/ LastTerm(log[i]) > LastTerm(log[w])
              \/ /\ LastTerm(log[i]) = LastTerm(log[w])
                 /\ Len(log[i]) >= Len(log[w])
              BY <3>5 DEF CanVoteForOplog
        \* All entries in i have term <= c[2] (from case assumption).
        <4>3. \A idx \in DOMAIN log[i] : log[i][idx] <= c[2]
              BY <3>7 DEF TypeOK, Terms
        \* So LastTerm(log[i]) <= c[2].
        <4>4. LastTerm(log[i]) <= c[2]
              BY <4>3 DEF LastTerm, TypeOK, Terms
        \* By H_TermsMonotonic on w, LastTerm(log[w]) >= c[2].
        <4>5. LastTerm(log[w]) >= c[2]
              BY <4>1 DEF H_TermsMonotonic, LastTerm, TypeOK, Terms
        \* From <4>2, case (a) contradicts <4>4 and <4>5, so must be case (b).
        <4>6. LastTerm(log[i]) = LastTerm(log[w]) /\ Len(log[i]) >= Len(log[w])
              BY <4>2, <4>4, <4>5 DEF LastTerm, TypeOK, Terms
        \* LastTerm(log[i]) = c[2], Len(log[i]) >= c[1].
        <4>7. LastTerm(log[i]) = c[2]
              BY <4>4, <4>5, <4>6 DEF LastTerm, TypeOK, Terms
        <4>8. Len(log[i]) >= c[1]
              BY <4>6, <4>1 DEF TypeOK
        \* c[1] is in DOMAIN log[i].
        <4>9. c[1] \in DOMAIN log[i]
              BY <4>8 DEF TypeOK, LogIndices, Terms
        \* i has term c[2] at position Len(log[i]) (from <4>7 + Len > 0).
        <4>10. Len(log[i]) > 0
               BY <4>8 DEF TypeOK, LogIndices, Terms
        <4>11. log[i][Len(log[i])] = c[2]
               BY <4>7, <4>10 DEF LastTerm, TypeOK
        \* By H_UniformLogEntries (w->i direction): the first occurrence of c[2] in w is at
        \* some position <= c[1]. c[2] cannot appear at a position < that in i.
        \* By H_UniformLogEntries (i->w direction): the first occurrence of c[2] in i
        \* cannot be before the first occurrence in w.
        \* Together: c[2] first appears at the same position in both, call it p, with p <= c[1].
        \* By monotonicity + all entries <= c[2], entries from p onward = c[2] in i. So log[i][c[1]] = c[2].
        \* The first occurrence of c[2] in i's log is at some position p_i <= c[1].
        \* Proof: By H_UniformLogEntries on i at the first occurrence p_i of c[2]:
        \*   c[2] can't appear before p_i in w. But w has c[2] at c[1].
        \*   So p_i <= c[1] (otherwise w has c[2] at c[1] < p_i, contradicting H_UniformLogEntries).
        \* By monotonicity + all entries in i have term <= c[2], entries from p_i onward = c[2].
        \* Since p_i <= c[1] <= Len(log[i]), log[i][c[1]] = c[2].
        \* c[2] appears at Len(log[i]) in i's log.
        <4>12. Len(log[i]) \in DOMAIN log[i] /\ log[i][Len(log[i])] = c[2]
               BY <4>10, <4>11 DEF TypeOK
        \* By H_UniformLogEntries on i at c[1]: if c[1] were the first occurrence of
        \* log[i][c[1]] in i, then log[i][c[1]] can't appear before c[1] in w.
        \* We use the contrapositive to show log[i][c[1]] = c[2].
        \* Suppose log[i][c[1]] # c[2], i.e. log[i][c[1]] < c[2] (since all <= c[2]).
        \* Then c[2] appears in i's log (at Len(log[i])) but not at c[1].
        \* By H_UniformLogEntries on i at the first occ of c[2] (call it p_i):
        \*   p_i >= c[1]+1 would require c[2] not to appear before p_i in w,
        \*   but w has c[2] at c[1] < p_i. Contradiction.
        \* So p_i <= c[1]. But log[i][c[1]] < c[2] and p_i <= c[1] means
        \* log[i][p_i] = c[2] > log[i][c[1]], contradicting monotonicity since p_i <= c[1].
        \* Therefore log[i][c[1]] = c[2].
        <4>13. log[i][c[1]] = c[2]
          <5>1. log[i][c[1]] <= c[2] BY <4>3, <4>9
          <5>1a. log[i][c[1]] \in Nat /\ c[2] \in Nat BY <4>9 DEF TypeOK, LogIndices, Terms
          <5>2. SUFFICES ~(log[i][c[1]] < c[2])
                BY <5>1, <5>1a
          \* Assume for contradiction that log[i][c[1]] < c[2].
          <5>3. SUFFICES ASSUME log[i][c[1]] < c[2] PROVE FALSE
                OBVIOUS
          \* By H_UniformLogEntries on i: for any position p in i's log where c[2] appears,
          \* if p is the first occurrence of c[2], then c[2] can't appear before p in w.
          \* We know c[2] appears at Len(log[i]) in i. Consider the first occ of c[2] in i.
          \* By monotonicity: since log[i][c[1]] < c[2] and log[i][Len(log[i])] = c[2],
          \* the first occ of c[2] is at some position p with c[1] < p <= Len(log[i]).
          \* By H_UniformLogEntries on i at p: c[2] doesn't appear before p in w.
          \* But w has c[2] at c[1] < p. Contradiction.
          <5>4. c[1] < Len(log[i]) \/ c[1] = Len(log[i])
                BY <4>8 DEF TypeOK, Terms
          <5>5. CASE c[1] = Len(log[i])
                \* log[i][c[1]] = log[i][Len(log[i])] = c[2], contradicting <5>3.
                BY <5>5, <5>3, <4>11 DEF LastTerm, TypeOK, Terms
          <5>6. CASE c[1] < Len(log[i])
            \* The set of positions in i's log with term c[2] is non-empty (Len(log[i]) is one).
            <6>. DEFINE S == {k \in DOMAIN log[i] : log[i][k] = c[2]}
            <6>1. S \subseteq Nat BY DEF TypeOK
            <6>2. S # {} BY <4>12
            \* Pick the minimum element p (first occurrence of c[2] in i's log).
            <6>3. PICK p \in S : \A m \in S : p <= m BY <6>1, <6>2, MinNatInSubset
            <6>4. p \in DOMAIN log[i] /\ log[i][p] = c[2] BY <6>3
            <6>5. \A m \in DOMAIN log[i] : log[i][m] = c[2] => p <= m BY <6>3
            \* p > c[1] because log[i][c[1]] < c[2] # log[i][p].
            <6>6. p > c[1]
                  BY <6>4, <4>9, <5>3 DEF H_TermsMonotonic, TypeOK, Terms
            \* All positions before p in i's log have term # c[2] (p is the first).
            <6>7. \A j \in DOMAIN log[i] : j < p => log[i][j] # log[i][p]
                  BY <6>4, <6>5 DEF TypeOK, Terms
            \* By H_UniformLogEntries on i at p: c[2] can't appear before p in w's log.
            <6>8. ~\E k \in DOMAIN log[w] : log[w][k] = log[i][p] /\ k < p
                  BY <6>4, <6>7 DEF H_UniformLogEntries, TypeOK
            \* But w has c[2] at c[1], and c[1] < p. Contradiction.
            <6>. QED BY <6>4, <6>6, <6>8, <4>1 DEF TypeOK, Terms
          <5>. QED BY <5>4, <5>5, <5>6
        <4>. QED BY <4>9, <4>13 DEF InLog
      <3>. QED BY <3>6, <3>7
    <2>. QED BY <2>1, <2>4, <2>5, <2>6, <2>7, <2>8, A7 DEF H_LeaderCompleteness, InLog, TypeOK
  \* (H_LeaderCompleteness,CommitEntryAction)
  <1>5. TypeOK /\ H_TermsMonotonic /\ H_QuorumsSafeAtTerms /\ H_LeaderCompleteness /\ CommitEntryAction => H_LeaderCompleteness'
    <2>. SUFFICES ASSUME TypeOK, H_TermsMonotonic, H_QuorumsSafeAtTerms, H_LeaderCompleteness,
                        NEW s \in Server, NEW Q \in Quorums(Server), CommitEntry(s, Q)
         PROVE H_LeaderCompleteness'
         BY DEF CommitEntryAction
    <2>1. UNCHANGED <<currentTerm, state, log>> BY DEF CommitEntry
    <2>2. state[s] = Primary BY DEF CommitEntry
    <2>3. immediatelyCommitted' = immediatelyCommitted \cup {<<Len(log[s]), currentTerm[s]>>}
          BY DEF CommitEntry
    \* All Q members have currentTerm = currentTerm[s]. Any primary p with currentTerm[p] > currentTerm[s]
    \* would need a quorum with terms >= currentTerm[p], but that quorum overlaps Q,
    \* giving a member with both currentTerm = currentTerm[s] and >= currentTerm[p]. Contradiction.
    <2>4. \A n \in Q : currentTerm[n] = currentTerm[s] BY DEF CommitEntry, ImmediatelyCommitted
    <2>5. \A p \in Server : state[p] = Primary /\ currentTerm[p] > currentTerm[s] => FALSE
      <3>. SUFFICES ASSUME NEW p \in Server, state[p] = Primary, currentTerm[p] > currentTerm[s]
           PROVE FALSE OBVIOUS
      <3>1. \E Q2 \in Quorums(Server) : \A n \in Q2 : currentTerm[n] >= currentTerm[p]
            BY DEF H_QuorumsSafeAtTerms
      <3>2. PICK Q2 \in Quorums(Server) : \A n \in Q2 : currentTerm[n] >= currentTerm[p]
            BY <3>1
      <3>3. Q \cap Q2 # {} BY <3>2, StaticQuorumsOverlap
      <3>4. PICK w \in Q \cap Q2 : TRUE BY <3>3
      <3>5. currentTerm[w] = currentTerm[s] BY <3>4, <2>4
      <3>6. currentTerm[w] >= currentTerm[p] BY <3>4, <3>2
      <3>. QED BY <3>5, <3>6 DEF TypeOK, Terms
    <2>. QED BY <2>1, <2>3, <2>5 DEF H_LeaderCompleteness, TypeOK, Terms
  \* (H_LeaderCompleteness,UpdateTermsAction)
  <1>6. TypeOK /\ H_LeaderCompleteness /\ UpdateTermsAction => H_LeaderCompleteness'
    <2>. SUFFICES ASSUME TypeOK, H_LeaderCompleteness,
                        NEW s \in Server, NEW t \in Server, UpdateTerms(s, t)
         PROVE H_LeaderCompleteness'
         BY DEF UpdateTermsAction
    <2>1. state'[t] = Secondary BY DEF UpdateTerms, UpdateTermsExpr, TypeOK
    <2>2. UNCHANGED <<log, immediatelyCommitted>> BY DEF UpdateTerms, UpdateTermsExpr
    <2>3. \A p \in Server : state'[p] = Primary => p # t BY <2>1, A7
    <2>4. \A p \in Server : state'[p] = Primary => state[p] = Primary /\ currentTerm'[p] = currentTerm[p]
          BY <2>3 DEF UpdateTerms, UpdateTermsExpr, TypeOK
    <2>. QED BY <2>2, <2>4 DEF H_LeaderCompleteness, TypeOK
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_LaterLogsHaveEarlierCommitted
THEOREM L_10 == TypeOK /\ H_LeaderCompleteness /\ H_TermsMonotonic /\ H_UniformLogEntries /\ H_LogEntryImpliesSafeAtTerm /\ H_LaterLogsHaveEarlierCommitted /\ Next => H_LaterLogsHaveEarlierCommitted'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_LaterLogsHaveEarlierCommitted,ClientRequestAction)
  <1>1. TypeOK /\ H_LeaderCompleteness /\ H_LaterLogsHaveEarlierCommitted /\ ClientRequestAction => H_LaterLogsHaveEarlierCommitted'
    <2>. SUFFICES ASSUME TypeOK, H_LeaderCompleteness, H_LaterLogsHaveEarlierCommitted,
                        NEW cr \in Server, ClientRequest(cr)
         PROVE H_LaterLogsHaveEarlierCommitted'
         BY DEF ClientRequestAction
    <2>1. state[cr] = Primary BY DEF ClientRequest
    <2>2. log' = [log EXCEPT ![cr] = Append(log[cr], currentTerm[cr])] BY DEF ClientRequest
    <2>3. UNCHANGED <<currentTerm, state, immediatelyCommitted>> BY DEF ClientRequest
    <2>4. \A s \in Server : s # cr => log'[s] = log[s] BY <2>2 DEF TypeOK
    <2>5. \A k \in DOMAIN log[cr] : log'[cr][k] = log[cr][k] BY <2>2 DEF TypeOK
    <2>6. Len(log'[cr]) = Len(log[cr]) + 1 BY <2>2 DEF TypeOK
    \* For s # cr: log unchanged, immediatelyCommitted unchanged, use pre-state.
    \* For s = cr: the new entry is currentTerm[cr]. If currentTerm[cr] > c[2] for some c,
    \* H_LeaderCompleteness (cr is Primary) gives log[cr][c[1]] = c[2], and log'[cr][c[1]] = log[cr][c[1]].
    <2>7. \A c \in immediatelyCommitted : c[2] < currentTerm[cr] => InLog(<<c[1],c[2]>>, cr)
          BY <2>1 DEF H_LeaderCompleteness
    \* For s = cr and c where the triggering entry with term > c[2] is in the OLD log[cr]:
    \* H_LaterLogsHaveEarlierCommitted on cr gives it.
    \* For s = cr and c where the trigger is the NEW entry (currentTerm[cr] > c[2]):
    \* H_LeaderCompleteness gives InLog(c, cr), which means log[cr][c[1]] = c[2], preserved by append.
    <2>8. \A c \in immediatelyCommitted :
            (\E ii \in DOMAIN log[cr] : log[cr][ii] > c[2]) => Len(log[cr]) >= c[1] /\ log[cr][c[1]] = c[2]
          BY DEF H_LaterLogsHaveEarlierCommitted
    \* Prove the s=cr case: any committed c with an entry in log'[cr] having term > c[2].
    \* Prove H_LaterLogsHaveEarlierCommitted' by picking arbitrary s, c.
    <2>. SUFFICES ASSUME NEW s \in Server, NEW c \in immediatelyCommitted,
                        \E ii \in DOMAIN log'[s] : log'[s][ii] > c[2]
         PROVE Len(log'[s]) >= c[1] /\ log'[s][c[1]] = c[2]
         BY <2>3 DEF H_LaterLogsHaveEarlierCommitted
    <2>9. CASE s # cr
      BY <2>1, <2>3, <2>4, <2>9 DEF H_LaterLogsHaveEarlierCommitted, TypeOK
    <2>10. CASE s = cr
      \* Either the triggering entry is in the old log, or it's the new entry.
      <3>1. CASE \E ii \in DOMAIN log[cr] : log[cr][ii] > c[2]
        \* Pre-state H_LaterLogsHaveEarlierCommitted on cr gives log[cr][c[1]] = c[2].
        <4>1. Len(log[cr]) >= c[1] /\ log[cr][c[1]] = c[2] BY <2>8, <3>1
        <4>2. c[1] \in DOMAIN log[cr] BY <4>1 DEF TypeOK, Terms, LogIndices
        <4>3. log'[cr][c[1]] = c[2] BY <4>1, <4>2, <2>5, <2>10 DEF TypeOK
        <4>4. Len(log'[cr]) >= c[1] BY <4>1, <2>6, <2>10 DEF TypeOK, Terms, LogIndices
        <4>. QED BY <4>3, <4>4, <2>10
      <3>2. CASE ~(\E ii \in DOMAIN log[cr] : log[cr][ii] > c[2])
        \* The new entry currentTerm[cr] > c[2], so c[2] < currentTerm[cr].
        \* H_LeaderCompleteness gives InLog(c, cr): log[cr][c[1]] = c[2].
        BY <2>1, <2>2, <2>5, <2>6, <2>7, <2>10, <3>2 DEF InLog, TypeOK, Terms
      <3>. QED BY <3>1, <3>2, <2>5, <2>10 DEF TypeOK
    <2>. QED BY <2>9, <2>10
  \* (H_LaterLogsHaveEarlierCommitted,GetEntriesAction)
  <1>2. TypeOK /\ H_TermsMonotonic /\ H_UniformLogEntries /\ H_LaterLogsHaveEarlierCommitted /\ GetEntriesAction => H_LaterLogsHaveEarlierCommitted'
    <2>. SUFFICES ASSUME TypeOK, H_TermsMonotonic, H_UniformLogEntries, H_LaterLogsHaveEarlierCommitted,
                        NEW gi \in Server, NEW gj \in Server, GetEntries(gi, gj)
         PROVE H_LaterLogsHaveEarlierCommitted'
         BY DEF GetEntriesAction
    <2>1. UNCHANGED <<currentTerm, state, immediatelyCommitted>> BY DEF GetEntries
    <2>2. \A s \in Server : s # gi => log'[s] = log[s] BY DEF GetEntries, Empty, TypeOK
    <2>3. \A k \in DOMAIN log[gi] : log'[gi][k] = log[gi][k] BY DEF GetEntries, Empty, TypeOK
    <2>4. Len(log'[gi]) = Len(log[gi]) + 1 BY DEF GetEntries, Empty, TypeOK
    \* For s # gi: log unchanged, use pre-state.
    <2>5. \A s \in Server : s # gi =>
            (\A c \in immediatelyCommitted : (\E ii \in DOMAIN log'[s] : log'[s][ii] > c[2]) =>
                Len(log'[s]) >= c[1] /\ log'[s][c[1]] = c[2])
          BY <2>1, <2>2 DEF H_LaterLogsHaveEarlierCommitted, TypeOK
    \* For s = gi: need to show the property for the extended log.
    <2>6. \A c \in immediatelyCommitted : (\E ii \in DOMAIN log'[gi] : log'[gi][ii] > c[2]) =>
            Len(log'[gi]) >= c[1] /\ log'[gi][c[1]] = c[2]
      <3>. SUFFICES ASSUME NEW c \in immediatelyCommitted,
                           NEW ii \in DOMAIN log'[gi], log'[gi][ii] > c[2]
           PROVE Len(log'[gi]) >= c[1] /\ log'[gi][c[1]] = c[2]
           OBVIOUS
      \* Case 1: the triggering entry ii is an old entry in log[gi].
      <3>1. CASE ii \in DOMAIN log[gi]
            \* Old entry preserved, pre-state H_LaterLogsHaveEarlierCommitted gives the result.
            BY <3>1, <2>3, <2>4 DEF H_LaterLogsHaveEarlierCommitted, TypeOK, Terms, LogIndices
      \* Case 2: the triggering entry is the new entry at Len(log[gi]) + 1.
      <3>2. CASE ii \notin DOMAIN log[gi]
        \* ii is the new entry position: ii = Len(log[gi]) + 1.
        <4>1. ii = Len(log[gi]) + 1
              BY <3>2, <2>4 DEF TypeOK
        \* The new entry = log[gj][Len(log[gi])+1], which has term > c[2].
        <4>2. Len(log[gj]) > Len(log[gi]) BY DEF GetEntries, TypeOK
        <4>3. Len(log[gi]) + 1 \in DOMAIN log[gj] BY <4>2 DEF TypeOK
        <4>4. log[gj][Len(log[gi]) + 1] > c[2]
              BY <4>1, <2>3, <2>4, <4>3 DEF GetEntries, Empty, TypeOK
        \* So gj has an entry with term > c[2]. By H_LaterLogsHaveEarlierCommitted on gj:
        <4>5. Len(log[gj]) >= c[1] /\ log[gj][c[1]] = c[2]
              BY <4>3, <4>4 DEF H_LaterLogsHaveEarlierCommitted
        \* c[1] can't be the new position (newEntry > c[2] # c[2]), so c[1] <= Len(log[gi]).
        \* c[2] and the new entry are naturals.
        <4>6. c[2] \in Nat /\ c[1] \in Nat /\ log[gj][Len(log[gi]) + 1] \in Nat
             BY <4>3 DEF TypeOK
        \* If c[1] = Len(log[gi])+1 then log[gj][c[1]] = c[2] and log[gj][c[1]] > c[2]. Contradiction.
        <4>7. c[1] # Len(log[gi]) + 1
             BY <4>4, <4>5, <4>6
        \* So c[1] <= Len(log[gj]) and c[1] # Len(log[gi])+1 and Len(log[gj]) > Len(log[gi]).
        \* We need c[1] <= Len(log[gi]), i.e. c[1] is in the old part of gi's log.
        \* By H_TermsMonotonic on gj: if c[1] > Len(log[gi])+1 then
        \* log[gj][Len(log[gi])+1] <= log[gj][c[1]] = c[2], contradicting log[gj][Len(log[gi])+1] > c[2].
        \* So c[1] <= Len(log[gi])+1. Combined with <4>7: c[1] <= Len(log[gi]).
        <4>8. c[1] <= Len(log[gi])
             BY <4>3, <4>4, <4>5, <4>6, <4>7 DEF H_TermsMonotonic, TypeOK, Terms, LogIndices
        <4>9. c[1] \in DOMAIN log[gi] BY <4>8 DEF TypeOK, Terms, LogIndices
        <4>10. log'[gi][c[1]] = log[gi][c[1]] BY <4>9, <2>3
        <4>11. Len(log'[gi]) >= c[1] BY <4>8, <2>4 DEF TypeOK, Terms
        \* Need log[gi][c[1]] = c[2]. Case split on whether gi already has an entry > c[2].
        <4>12. CASE \E idx \in DOMAIN log[gi] : log[gi][idx] > c[2]
               \* Pre-state H_LaterLogsHaveEarlierCommitted on gi gives the result.
               BY <4>10, <4>11, <4>12 DEF H_LaterLogsHaveEarlierCommitted
        <4>13. CASE ~\E idx \in DOMAIN log[gi] : log[gi][idx] > c[2]
          \* All entries in gi have term <= c[2].
          <5>1. \A idx \in DOMAIN log[gi] : log[gi][idx] <= c[2]
                BY <4>13 DEF TypeOK, Terms
          <5>2. log[gi][c[1]] <= c[2] BY <5>1, <4>9
          \* Prove log[gi][c[1]] = c[2] by contradiction. Assume log[gi][c[1]] < c[2].
          <5>3. SUFFICES ASSUME log[gi][c[1]] < c[2] PROVE FALSE
                BY <5>2, <4>6, <4>9, <4>10, <4>11 DEF TypeOK, Terms
          \* The log consistency check in GetEntries: log[gj][Len(log[gi])] = log[gi][Len(log[gi])]
          \* (when log[gi] non-empty). Since Len(log[gi]) >= c[1] >= 1, log[gi] is non-empty.
          <5>4. Len(log[gi]) >= 1
                BY <4>8 DEF TypeOK, Terms, LogIndices
          <5>5. log[gj][Len(log[gi])] = log[gi][Len(log[gi])]
                BY <5>4 DEF GetEntries, Empty, TypeOK
          \* By H_TermsMonotonic on gj: log[gj][c[1]] <= log[gj][Len(log[gi])] (since c[1] <= Len(log[gi])).
          \* log[gj][c[1]] = c[2], so c[2] <= log[gj][Len(log[gi])] = log[gi][Len(log[gi])].
          <5>6. Len(log[gi]) \in DOMAIN log[gj] BY <4>2, <5>4 DEF TypeOK
          <5>7. c[1] \in DOMAIN log[gj] BY <4>5 DEF TypeOK, Terms, LogIndices
          <5>8. log[gj][c[1]] <= log[gj][Len(log[gi])]
                BY <5>6, <5>7, <4>8 DEF H_TermsMonotonic, TypeOK
          <5>9. c[2] <= log[gi][Len(log[gi])]
                BY <5>8, <5>5, <4>5
          \* So log[gi][Len(log[gi])] >= c[2]. But all entries in gi have term <= c[2].
          \* So log[gi][Len(log[gi])] = c[2]. gi has term c[2] at Len(log[gi]).
          <5>10. Len(log[gi]) \in DOMAIN log[gi] BY <5>4 DEF TypeOK
          <5>11. log[gi][Len(log[gi])] <= c[2] BY <5>1, <5>10
          <5>12. log[gi][Len(log[gi])] = c[2]
                 BY <5>9, <5>11, <5>10, <4>6 DEF TypeOK, Terms
          \* Now: log[gi][c[1]] < c[2] = log[gi][Len(log[gi])], and c[1] <= Len(log[gi]).
          \* Same MinNatInSubset argument: find first occurrence of c[2] in gj at position p,
          \* by H_UniformLogEntries c[2] can't appear before p in gi. p <= c[1].
          \* But gi has c[2] at Len(log[gi]) >= c[1] >= p. So first occ of c[2] in gi is at some q >= p.
          \* Since log[gi][c[1]] < c[2], q # c[1], so q > c[1] (since q >= p and either q < c[1] or q > c[1]).
          \* Wait, q could be < c[1] too (if p < c[1] and there's an earlier occurrence).
          \* Actually by H_UniformLogEntries first occ of c[2] in gi must be >= p,
          \* and by H_UniformLogEntries on gi at that first occ, c[2] can't appear before it in gj.
          \* But gj has c[2] at p. So first occ of c[2] in gi >= p, and p can't be before first occ of c[2] in gi.
          \* Wait this means first occ of c[2] in gi = first occ of c[2] in gj = p.
          \* So log[gi][p] = c[2] with p <= c[1].
          \* By H_TermsMonotonic on gi: log[gi][p] <= log[gi][c[1]]. So c[2] <= log[gi][c[1]].
          \* But log[gi][c[1]] < c[2]. Contradiction!
          <5>. DEFINE Sgj == {k \in DOMAIN log[gj] : log[gj][k] = c[2]}
          <5>13. Sgj \subseteq Nat BY DEF TypeOK
          <5>14. Sgj # {} BY <5>7, <4>5
          <5>15. PICK p \in Sgj : \A m \in Sgj : p <= m BY <5>13, <5>14, MinNatInSubset
          <5>16. p \in DOMAIN log[gj] /\ log[gj][p] = c[2] BY <5>15
          <5>17. p <= c[1] BY <5>15, <5>7, <4>5
          \* All positions before p in gj have term # c[2].
          <5>18. \A j \in DOMAIN log[gj] : j < p => log[gj][j] # log[gj][p]
                 BY <5>16, <5>15 DEF TypeOK, Terms
          \* By H_UniformLogEntries on gj at p: c[2] can't appear before p in gi.
          <5>19. ~\E k \in DOMAIN log[gi] : log[gi][k] = c[2] /\ k < p
                 BY <5>16, <5>18 DEF H_UniformLogEntries, TypeOK
          \* gi has c[2] at Len(log[gi]) (from <5>12). First occ of c[2] in gi is at some q.
          <5>. DEFINE Sgi == {k \in DOMAIN log[gi] : log[gi][k] = c[2]}
          <5>20. Sgi \subseteq Nat BY DEF TypeOK
          <5>21. Sgi # {} BY <5>10, <5>12
          <5>22. PICK q \in Sgi : \A m \in Sgi : q <= m BY <5>20, <5>21, MinNatInSubset
          <5>23. q \in DOMAIN log[gi] /\ log[gi][q] = c[2] BY <5>22
          \* q >= p (from <5>19: c[2] doesn't appear before p in gi).
          <5>24. q >= p BY <5>19, <5>23 DEF TypeOK, Terms
          \* By H_UniformLogEntries on gi at q: c[2] can't appear before q in gj.
          <5>25. \A j \in DOMAIN log[gi] : j < q => log[gi][j] # log[gi][q]
                 BY <5>22, <5>23 DEF TypeOK, Terms
          <5>26. ~\E k \in DOMAIN log[gj] : log[gj][k] = c[2] /\ k < q
                 BY <5>23, <5>25 DEF H_UniformLogEntries, TypeOK
          \* But gj has c[2] at p. So p >= q. Combined with q >= p: q = p.
          <5>27. p >= q BY <5>26, <5>16 DEF TypeOK, Terms
          <5>28. q = p BY <5>24, <5>27 DEF TypeOK, Terms
          \* So log[gi][p] = c[2] with p <= c[1].
          \* By H_TermsMonotonic on gi: log[gi][p] <= log[gi][c[1]].
          <5>29. log[gi][p] = c[2] BY <5>23, <5>28
          <5>30. p <= c[1] BY <5>17
          <5>31. log[gi][p] <= log[gi][c[1]]
                 BY <5>23, <5>28, <4>9, <5>30 DEF H_TermsMonotonic, TypeOK
          \* c[2] <= log[gi][c[1]], contradicting log[gi][c[1]] < c[2].
          <5>32. log[gi][c[1]] \in Nat BY <4>9 DEF TypeOK, Terms
          <5>. QED BY <5>29, <5>31, <5>3, <5>32, <4>6
        <4>. QED BY <4>12, <4>13
      <3>. QED BY <3>1, <3>2
    <2>. QED BY <2>1, <2>5, <2>6 DEF H_LaterLogsHaveEarlierCommitted
  \* (H_LaterLogsHaveEarlierCommitted,RollbackEntriesAction)
  <1>3. TypeOK /\ H_TermsMonotonic /\ H_LaterLogsHaveEarlierCommitted /\ RollbackEntriesAction => H_LaterLogsHaveEarlierCommitted'
    <2>. SUFFICES ASSUME TypeOK, H_TermsMonotonic, H_LaterLogsHaveEarlierCommitted,
                        NEW ri \in Server, NEW rj \in Server, RollbackEntries(ri, rj)
         PROVE H_LaterLogsHaveEarlierCommitted'
         BY DEF RollbackEntriesAction
    <2>1. UNCHANGED <<currentTerm, state, immediatelyCommitted>> BY DEF RollbackEntries
    <2>2. log' = [log EXCEPT ![ri] = SubSeq(log[ri], 1, Len(log[ri])-1)] BY DEF RollbackEntries, CanRollback
    <2>3. \A s \in Server : s # ri => log'[s] = log[s] BY <2>2 DEF TypeOK
    \* For s # ri: unchanged, pre-state applies.
    \* For s = ri: log'[ri] is a prefix of log[ri]. If \E ii \in DOMAIN log'[ri] : log'[ri][ii] > c[2],
    \* then that entry is also in DOMAIN log[ri] with same value, so pre-state applies.
    <2>. SUFFICES ASSUME NEW s \in Server, NEW c \in immediatelyCommitted,
                        \E ii \in DOMAIN log'[s] : log'[s][ii] > c[2]
         PROVE Len(log'[s]) >= c[1] /\ log'[s][c[1]] = c[2]
         BY <2>1 DEF H_LaterLogsHaveEarlierCommitted
    <2>4. CASE s # ri
      BY <2>1, <2>3, <2>4 DEF H_LaterLogsHaveEarlierCommitted, TypeOK
    <2>5. CASE s = ri
      \* log'[ri] = SubSeq(log[ri], 1, Len(log[ri])-1). Entries in log'[ri] are in log[ri].
      \* H_TermsMonotonic ensures c[1] < Len(log[ri]) (since triggering entry at ii < Len(log[ri])
      \* has term > c[2], but log[ri][Len(log[ri])] >= log[ri][ii] > c[2] by monotonicity,
      \* contradicting log[ri][c[1]] = c[2] if c[1] = Len(log[ri])).
      BY <2>1, <2>2, <2>5 DEF H_LaterLogsHaveEarlierCommitted, H_TermsMonotonic, TypeOK, Terms, LogIndices
    <2>. QED BY <2>4, <2>5
  \* (H_LaterLogsHaveEarlierCommitted,BecomeLeaderAction)
  <1>4. TypeOK /\ H_LaterLogsHaveEarlierCommitted /\ BecomeLeaderAction => H_LaterLogsHaveEarlierCommitted' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_LaterLogsHaveEarlierCommitted
  \* (H_LaterLogsHaveEarlierCommitted,CommitEntryAction)
  <1>5. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ H_LaterLogsHaveEarlierCommitted /\ CommitEntryAction => H_LaterLogsHaveEarlierCommitted'
    <2>. SUFFICES ASSUME TypeOK, H_LogEntryImpliesSafeAtTerm, H_LaterLogsHaveEarlierCommitted,
                        NEW cs \in Server, NEW cQ \in Quorums(Server), CommitEntry(cs, cQ)
         PROVE H_LaterLogsHaveEarlierCommitted'
         BY DEF CommitEntryAction
    <2>1. UNCHANGED <<currentTerm, state, log>> BY DEF CommitEntry
    <2>2. \A n \in cQ : currentTerm[n] = currentTerm[cs] BY DEF CommitEntry, ImmediatelyCommitted
    \* No server has an entry with term > currentTerm[cs].
    \* Proof: by H_LogEntryImpliesSafeAtTerm, such entry has quorum with terms >= that > currentTerm[cs].
    \* That quorum overlaps cQ, giving member with currentTerm = currentTerm[cs] >= something > currentTerm[cs].
    <2>3. \A s2 \in Server : ~(\E ii \in DOMAIN log[s2] : log[s2][ii] > currentTerm[cs])
      <3>. SUFFICES ASSUME NEW s2 \in Server, NEW ii \in DOMAIN log[s2], log[s2][ii] > currentTerm[cs]
           PROVE FALSE OBVIOUS
      <3>1. \E Q2 \in Quorums(Server) : \A n \in Q2 : currentTerm[n] >= log[s2][ii]
            BY DEF H_LogEntryImpliesSafeAtTerm
      <3>2. PICK Q2 \in Quorums(Server) : \A n \in Q2 : currentTerm[n] >= log[s2][ii] BY <3>1
      <3>3. cQ \cap Q2 # {} BY <3>2, StaticQuorumsOverlap
      <3>4. PICK w \in cQ \cap Q2 : TRUE BY <3>3
      <3>5. currentTerm[w] = currentTerm[cs] BY <3>4, <2>2
      <3>6. currentTerm[w] >= log[s2][ii] BY <3>4, <3>2
      <3>. QED BY <3>5, <3>6 DEF TypeOK, Terms
    \* The new committed entry vacuously satisfies the condition (no entry has term > currentTerm[cs]).
    \* Old committed entries: log unchanged, use pre-state.
    <2>. QED BY <2>1, <2>3 DEF H_LaterLogsHaveEarlierCommitted, CommitEntry, TypeOK, Terms
  \* (H_LaterLogsHaveEarlierCommitted,UpdateTermsAction)
  <1>6. TypeOK /\ H_LaterLogsHaveEarlierCommitted /\ UpdateTermsAction => H_LaterLogsHaveEarlierCommitted' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_LaterLogsHaveEarlierCommitted
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_CommittedEntryIsOnQuorum
THEOREM L_11 == TypeOK /\ H_LaterLogsHaveEarlierCommitted /\ H_CommittedEntryIsOnQuorum /\ Next => H_CommittedEntryIsOnQuorum'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_CommittedEntryIsOnQuorum,ClientRequestAction)
  <1>1. TypeOK /\ H_CommittedEntryIsOnQuorum /\ ClientRequestAction => H_CommittedEntryIsOnQuorum' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_CommittedEntryIsOnQuorum,InLog
  \* (H_CommittedEntryIsOnQuorum,GetEntriesAction)
  <1>2. TypeOK /\ H_CommittedEntryIsOnQuorum /\ GetEntriesAction => H_CommittedEntryIsOnQuorum'
    <2>. SUFFICES ASSUME TypeOK, H_CommittedEntryIsOnQuorum,
                        NEW gi \in Server, NEW gj \in Server, GetEntries(gi, gj)
         PROVE H_CommittedEntryIsOnQuorum'
         BY DEF GetEntriesAction
    <2>1. UNCHANGED <<currentTerm, state, immediatelyCommitted>> BY DEF GetEntries
    <2>2. \A s \in Server : s # gi => log'[s] = log[s] BY DEF GetEntries, Empty, TypeOK
    <2>3. \A k \in DOMAIN log[gi] : log'[gi][k] = log[gi][k] BY DEF GetEntries, Empty, TypeOK
    <2>4. DOMAIN log[gi] \subseteq DOMAIN log'[gi] BY DEF GetEntries, Empty, TypeOK
    \* For each committed entry c, pre-state quorum Q has all members with InLog(c, n).
    \* After GetEntries, for n # gi: log unchanged. For n = gi: old entries preserved by <2>3>.
    <2>. QED BY <2>1, <2>2, <2>3, <2>4 DEF H_CommittedEntryIsOnQuorum, InLog, TypeOK
  \* (H_CommittedEntryIsOnQuorum,RollbackEntriesAction)
  <1>3. TypeOK /\ H_LaterLogsHaveEarlierCommitted /\ H_CommittedEntryIsOnQuorum /\ RollbackEntriesAction => H_CommittedEntryIsOnQuorum'
    <2>. SUFFICES ASSUME TypeOK, H_LaterLogsHaveEarlierCommitted, H_CommittedEntryIsOnQuorum,
                        NEW i \in Server, NEW j \in Server, RollbackEntries(i, j)
         PROVE H_CommittedEntryIsOnQuorum'
         BY DEF RollbackEntriesAction
    <2>1. UNCHANGED <<currentTerm, state, immediatelyCommitted>> BY DEF RollbackEntries
    <2>2. log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i])-1)] BY DEF RollbackEntries, CanRollback
    <2>3. Len(log[i]) > 0 BY DEF RollbackEntries, CanRollback
    <2>4. LastTerm(log[i]) < LastTerm(log[j]) BY DEF RollbackEntries, CanRollback
    <2>5. \A s \in Server : s # i => log'[s] = log[s] BY <2>2 DEF TypeOK
    <2>6. i # j BY DEF RollbackEntries, CanRollback, LastTerm, TypeOK, Terms
    \* j has higher LastTerm, so by H_LaterLogsHaveEarlierCommitted on j,
    \* j has all committed entries. And log'[j] = log[j]. So j still has them.
    \* For each committed entry c on quorum Q, all Q members have the entry.
    \* Show that for any committed entry c on quorum Qc, if i \in Qc then c[1] # Len(log[i]).
    \* This means the entry at c[1] survives the truncation, so the same quorum works.
    \* Proof: assume c[1] = Len(log[i]) for contradiction.
    \*   log[i][c[1]] = c[2], so LastTerm(log[i]) = log[i][Len(log[i])] = c[2] (if c[1] = Len(log[i])).
    \*   Wait, LastTerm(log[i]) is the LAST entry, which equals c[2].
    \*   CanRollback case 1: Len(log[i]) > Len(log[j]) and LastTerm(log[i]) < LastTerm(log[j]).
    \*     LastTerm(log[j]) > c[2]. H_LaterLogsHaveEarlierCommitted on j: Len(log[j]) >= c[1] = Len(log[i]).
    \*     But Len(log[i]) > Len(log[j]) — contradiction.
    \*   CanRollback case 2: Len(log[i]) <= Len(log[j]) and log[j][Len(log[i])] # log[i][Len(log[i])] = c[2].
    \*     LastTerm(log[j]) > LastTerm(log[i]) = c[2]. H_LaterLogsHaveEarlierCommitted on j: log[j][c[1]] = c[2].
    \*     But log[j][Len(log[i])] # c[2], and c[1] = Len(log[i]) — contradiction.
    <2>7. \A c \in immediatelyCommitted : InLog(<<c[1],c[2]>>, i) => c[1] # Len(log[i])
      <3>. SUFFICES ASSUME NEW c \in immediatelyCommitted, InLog(<<c[1],c[2]>>, i), c[1] = Len(log[i])
           PROVE FALSE OBVIOUS
      <3>1. log[i][Len(log[i])] = c[2] BY DEF InLog
      <3>2. LastTerm(log[i]) = c[2] BY <2>3, <3>1 DEF LastTerm
      <3>3. LastTerm(log[j]) > c[2] BY <2>4, <3>2
      \* j has entry with term > c[2], so H_LaterLogsHaveEarlierCommitted on j gives:
      <3>4. Len(log[j]) >= c[1] /\ log[j][c[1]] = c[2]
        <4>1. \E ii \in DOMAIN log[j] : log[j][ii] > c[2]
              BY <3>3 DEF LastTerm, TypeOK, Terms
        <4>. QED BY <4>1 DEF H_LaterLogsHaveEarlierCommitted
      \* Now derive contradiction from CanRollback.
      \* CanRollback case 1: Len(log[i]) > Len(log[j]). But Len(log[j]) >= c[1] = Len(log[i]). Contradiction.
      \* CanRollback case 2: Len(log[i]) <= Len(log[j]) and log[j][Len(log[i])] # log[i][Len(log[i])].
      \*   log[j][Len(log[i])] # c[2] (from CanRollback). But log[j][c[1]] = c[2] and c[1] = Len(log[i]). Contradiction.
      <3>. QED BY <2>3, <2>4, <3>1, <3>4 DEF CanRollback, LastTerm, LogTerm, GetTerm, RollbackEntries, TypeOK, Terms
    \* Now prove the main result.
    <2>. SUFFICES ASSUME NEW c \in immediatelyCommitted
         PROVE \E Qc \in Quorums(Server) : \A n \in Qc : InLog(<<c[1],c[2]>>, n)'
         BY <2>1 DEF H_CommittedEntryIsOnQuorum
    <2>8. PICK Qc \in Quorums(Server) : \A n \in Qc : InLog(<<c[1],c[2]>>, n)
          BY DEF H_CommittedEntryIsOnQuorum
    \* Show InLog(c, n)' for all n in Qc.
    <2>9. \A n \in Qc : InLog(<<c[1],c[2]>>, n)'
      <3>. SUFFICES ASSUME NEW n \in Qc PROVE InLog(<<c[1],c[2]>>, n)' OBVIOUS
      <3>1. InLog(<<c[1],c[2]>>, n) BY <2>8
      <3>2. CASE n # i
        BY <3>1, <3>2, <2>5 DEF InLog
      <3>3. CASE n = i
        \* c[1] # Len(log[i]) by <2>7, so c[1] < Len(log[i]), so c[1] \in DOMAIN log'[i].
        <4>1. c[1] # Len(log[i]) BY <2>7, <3>1, <3>3
        <4>2. c[1] \in DOMAIN log[i] BY <3>1, <3>3 DEF InLog
        <4>3. c[1] < Len(log[i]) BY <4>1, <4>2 DEF TypeOK, Terms, LogIndices
        <4>4. c[1] \in DOMAIN log'[i] BY <4>3, <2>2, <2>3, <3>3 DEF TypeOK, Terms, LogIndices
        <4>5. log'[i][c[1]] = log[i][c[1]] BY <4>3, <2>2, <2>3, <3>3 DEF TypeOK, Terms, LogIndices
        <4>. QED BY <3>1, <3>3, <4>4, <4>5 DEF InLog
      <3>. QED BY <3>2, <3>3
    <2>. QED BY <2>8, <2>9
  \* (H_CommittedEntryIsOnQuorum,BecomeLeaderAction)
  <1>4. TypeOK /\ H_CommittedEntryIsOnQuorum /\ BecomeLeaderAction => H_CommittedEntryIsOnQuorum' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_CommittedEntryIsOnQuorum,InLog
  \* (H_CommittedEntryIsOnQuorum,CommitEntryAction)
  <1>5. TypeOK /\ H_CommittedEntryIsOnQuorum /\ CommitEntryAction => H_CommittedEntryIsOnQuorum' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_CommittedEntryIsOnQuorum,InLog,ImmediatelyCommitted
  \* (H_CommittedEntryIsOnQuorum,UpdateTermsAction)
  <1>6. TypeOK /\ H_CommittedEntryIsOnQuorum /\ UpdateTermsAction => H_CommittedEntryIsOnQuorum' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,UpdateTermsExpr,H_CommittedEntryIsOnQuorum,InLog
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\* (ROOT SAFETY PROP)
\*** H_StateMachineSafety
THEOREM L_12 == TypeOK /\ H_CommittedEntryIsOnQuorum /\ H_StateMachineSafety /\ Next => H_StateMachineSafety'
  <1>. USE A0,A1,A2,A3,A4,A5,A6 DEF ImmediatelyCommitted, InLog
  \* (H_StateMachineSafety,ClientRequestAction)
  <1>1. TypeOK /\ H_StateMachineSafety /\ ClientRequestAction => H_StateMachineSafety' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_StateMachineSafety
  \* (H_StateMachineSafety,GetEntriesAction)
  <1>2. TypeOK /\ H_StateMachineSafety /\ GetEntriesAction => H_StateMachineSafety' BY DEF TypeOK,GetEntriesAction,GetEntries,H_StateMachineSafety
  \* (H_StateMachineSafety,RollbackEntriesAction)
  <1>3. TypeOK /\ H_StateMachineSafety /\ RollbackEntriesAction => H_StateMachineSafety' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_StateMachineSafety
  \* (H_StateMachineSafety,BecomeLeaderAction)
  <1>4. TypeOK /\ H_StateMachineSafety /\ BecomeLeaderAction => H_StateMachineSafety' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_StateMachineSafety
  \* (H_StateMachineSafety,CommitEntryAction)
  <1>5. TypeOK /\ H_CommittedEntryIsOnQuorum /\ H_StateMachineSafety /\ CommitEntryAction => H_StateMachineSafety'
    <2>. SUFFICES ASSUME TypeOK, H_CommittedEntryIsOnQuorum, H_StateMachineSafety,
                        NEW s \in Server, NEW Q \in Quorums(Server), CommitEntry(s, Q),
                        NEW c1 \in immediatelyCommitted', NEW c2 \in immediatelyCommitted',
                        c1[1] = c2[1]
         PROVE c1 = c2
         BY DEF CommitEntryAction, H_StateMachineSafety
    <2>1. UNCHANGED <<currentTerm, state, log>> BY DEF CommitEntry
    <2>2. immediatelyCommitted' = immediatelyCommitted \cup {<<Len(log[s]), currentTerm[s]>>}
          BY DEF CommitEntry
    <2>3. LET newC == <<Len(log[s]), currentTerm[s]>> IN
          \A n \in Q : InLog(newC, n) /\ currentTerm[n] = currentTerm[s]
          BY DEF CommitEntry, ImmediatelyCommitted
    \* Case 1: both old committed entries.
    <2>4. CASE c1 \in immediatelyCommitted /\ c2 \in immediatelyCommitted
      BY <2>4 DEF H_StateMachineSafety
    \* Case 2: c1 is new, c2 is old (or both new).
    \* The new entry <<ind, currentTerm[s]>> has quorum Q where all have InLog at index ind.
    \* By H_CommittedEntryIsOnQuorum, c2 has quorum Q2 where all have InLog at c2[1] = c1[1] = ind.
    \* Q \cap Q2 # {}, pick w. w has log[w][ind] = currentTerm[s] AND log[w][ind] = c2[2].
    \* So c2[2] = currentTerm[s] = c1[2], and c1[1] = c2[1], hence c1 = c2.
    <2>5. CASE c1 = <<Len(log[s]), currentTerm[s]>> /\ c2 \in immediatelyCommitted
      <3>1. PICK Q2 \in Quorums(Server) : \A n \in Q2 : InLog(<<c2[1],c2[2]>>, n)
            BY <2>5 DEF H_CommittedEntryIsOnQuorum
      <3>2. Q \cap Q2 # {} BY <3>1, StaticQuorumsOverlap
      <3>3. PICK w \in Q \cap Q2 : TRUE BY <3>2
      <3>4. InLog(<<Len(log[s]), currentTerm[s]>>, w) BY <3>3, <2>3
      <3>5. InLog(<<c2[1],c2[2]>>, w) BY <3>3, <3>1
      \* log[w][Len(log[s])] = currentTerm[s] and log[w][c2[1]] = c2[2]. Since c1[1] = c2[1] = Len(log[s]):
      <3>6. c2[2] = currentTerm[s] BY <3>4, <3>5, <2>5 DEF InLog
      <3>. QED BY <3>6, <2>5 DEF TypeOK, Terms, LogIndices
    <2>6. CASE c2 = <<Len(log[s]), currentTerm[s]>> /\ c1 \in immediatelyCommitted
      <3>1. PICK Q2 \in Quorums(Server) : \A n \in Q2 : InLog(<<c1[1],c1[2]>>, n)
            BY <2>6 DEF H_CommittedEntryIsOnQuorum
      <3>2. Q \cap Q2 # {} BY <3>1, StaticQuorumsOverlap
      <3>3. PICK w \in Q \cap Q2 : TRUE BY <3>2
      <3>4. InLog(<<Len(log[s]), currentTerm[s]>>, w) BY <3>3, <2>3
      <3>5. InLog(<<c1[1],c1[2]>>, w) BY <3>3, <3>1
      <3>6. c1[2] = currentTerm[s] BY <3>4, <3>5, <2>6 DEF InLog
      <3>. QED BY <3>6, <2>6 DEF TypeOK, Terms, LogIndices
    <2>7. CASE c1 = <<Len(log[s]), currentTerm[s]>> /\ c2 = <<Len(log[s]), currentTerm[s]>>
      BY <2>7
    <2>. QED BY <2>2, <2>4, <2>5, <2>6, <2>7
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
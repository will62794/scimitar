--------------------------------- MODULE AsyncRaft_IndProofs_OnePrimaryPerTerm_1 ---------------------------------
EXTENDS AsyncRaft,TLAPS, SequenceTheorems, FunctionTheorems, FiniteSetTheorems, FiniteSets

THEOREM FS_Doubleton ==
  /\ \A x,y : IsFiniteSet({x,y}) /\ Cardinality({x,y}) = 2
  /\ \A S : IsFiniteSet(S) => (Cardinality(S) = 2 <=> \E x,y: S = {x,y} /\ x # y)

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

LEMMA ServerStateType == 
    \A s \in Server : 
        /\ state[s] \in {Leader, Candidate, Follower}
        /\ state[s] # Follower <=> state[s] \in {Leader, Candidate}



\* Proof Graph Stats
\* ==================
\* seed: 1
\* num proof graph nodes: 13
\* num proof obligations: 117
Safety == H_OnePrimaryPerTerm
Inv42_d848_R0_0_I0 == \A VARI \in Server : \A VARJ \in Server : (~((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) \/ (~((state[VARJ] = Leader))) \/ (~(votesGranted[VARI] \in Quorum)))
Inv8_8e53_R1_0_I0 == (\A s,t \in Server : ( /\ s # t /\ state[s] \in {Leader,Candidate} /\ state[t] \in {Leader,Candidate} /\ currentTerm[s] = currentTerm[t]) => votesGranted[s] \cap votesGranted[t] = {})
Inv2907_928b_R1_1_I1 == \A VARI \in Server : (VARI \in votesGranted[VARI]) \/ ((votesGranted[VARI] = {}))
Inv4738_3acc_R1_1_I1 == \A VARI \in Server : (votesGranted[VARI] \in Quorum) \/ (~((state[VARI] = Leader)))
Inv27_42ac_R1_1_I1 == (\A s,t \in Server : \A m \in requestVoteResponseMsgs :( /\ state[s] \in {Candidate,Leader} /\ t \in votesGranted[s]) => ~(/\ m.mterm = currentTerm[s] /\ m.msource = t /\ m.mdest # s /\ m.mvoteGranted))
Inv0_2c32_R2_1_I1 == \A VARI \in Server : \A VARJ \in Server : ((currentTerm[VARI] <= currentTerm[VARJ])) \/ (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])))
Inv18_09bb_R3_0_I1 == \A VARI \in Server : \A VARREQVRES \in requestVoteResponseMsgs : ~(VARREQVRES.mdest = VARI) \/ (~(votesGranted[VARI] = {}))
Inv10_e30e_R5_0_I1 == \A VARI \in Server :  (((state[VARI] # Follower))) => ((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI ))
Inv9_82b3_R5_1_I0 == (\A mi,mj \in requestVoteResponseMsgs : (/\ mi.mterm = mj.mterm /\ mi.msource = mj.msource /\ mi.mvoteGranted /\ mj.mvoteGranted) => mi.mdest = mj.mdest)
Inv12_f533_R5_2_I0 == \A VARREQVRES \in requestVoteResponseMsgs : (currentTerm[VARREQVRES.msource] >= VARREQVRES.mterm)
Inv2349_f747_R7_0_I1 == \A VARJ \in Server : \A VARREQVM \in requestVoteRequestMsgs : (VARREQVM.msource = VARJ) => ((votesGranted[VARJ] # {}))
Inv9_3715_R8_0_I0 == (\A m \in requestVoteResponseMsgs : m.mtype = RequestVoteResponse =>  /\ (m.mvoteGranted /\ (currentTerm[m.msource] = m.mterm)) => votedFor[m.msource] = m.mdest)

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv42_d848_R0_0_I0
  /\ Inv8_8e53_R1_0_I0
  /\ Inv27_42ac_R1_1_I1
  /\ Inv10_e30e_R5_0_I1
  /\ Inv9_3715_R8_0_I0
  /\ Inv12_f533_R5_2_I0
  /\ Inv0_2c32_R2_1_I1
  /\ Inv9_82b3_R5_1_I0
  /\ Inv2907_928b_R1_1_I1
  /\ Inv18_09bb_R3_0_I1
  /\ Inv2349_f747_R7_0_I1
  /\ Inv4738_3acc_R1_1_I1


\* mean in-degree: 1.5384615384615385
\* median in-degree: 1
\* max in-degree: 5
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

USE ServerStateType, StaticQuorumsOverlap, QuorumsExistForNonEmptySets, AddingToQuorumRemainsQuorum, EmptyIntersectionImpliesNotBothQuorums, 
    FS_Subset, FS_Difference, FS_Singleton, FS_EmptySet

\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (TypeOK,RequestVoteAction)
  <1>1. TypeOK /\ TypeOK /\ RequestVoteAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ RequestVoteAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>2. (requestVoteResponseMsgs \in SUBSET RequestVoteResponseType)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>3. (appendEntriesRequestMsgs \in SUBSET AppendEntriesRequestType)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>4. (appendEntriesResponseMsgs \in SUBSET AppendEntriesResponseType)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>5. (currentTerm \in [Server -> Nat])'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>6. (state       \in [Server -> {Leader, Follower, Candidate}])'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>7. (votedFor    \in [Server -> ({Nil} \cup Server)])'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>8. (votesGranted \in [Server -> (SUBSET Server)])'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>9. (nextIndex  \in [Server -> [Server -> Nat]])'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>10. (matchIndex \in [Server -> [Server -> Nat]])'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>11. (log             \in [Server -> Seq(Nat)])'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>12. (commitIndex     \in [Server -> Nat])'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>13. (\A m \in requestVoteRequestMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>14. (\A m \in requestVoteResponseMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>15. (\A m \in appendEntriesRequestMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>16. (\A m \in appendEntriesResponseMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>17. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
  \* (TypeOK,UpdateTermAction)
  <1>2. TypeOK /\ TypeOK /\ UpdateTermAction => TypeOK' BY DEF TypeOK,UpdateTermAction,UpdateTerm,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (TypeOK,BecomeLeaderAction)
  <1>3. TypeOK /\ TypeOK /\ BecomeLeaderAction => TypeOK' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,TypeOK
  \* (TypeOK,ClientRequestAction)
  <1>4. TypeOK /\ TypeOK /\ ClientRequestAction => TypeOK' BY DEF TypeOK,ClientRequestAction,ClientRequest,TypeOK
  \* (TypeOK,AppendEntriesAction)
  <1>5. TypeOK /\ TypeOK /\ AppendEntriesAction => TypeOK' BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
  \* (TypeOK,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ TypeOK /\ HandleRequestVoteRequestAction => TypeOK' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (TypeOK,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ TypeOK /\ HandleRequestVoteResponseAction => TypeOK' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (TypeOK,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ TypeOK /\ AcceptAppendEntriesRequestAppendAction => TypeOK' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
  \* (TypeOK,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ TypeOK /\ HandleAppendEntriesResponseAction => TypeOK' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Inv42_d848_R0_0_I0 /\ Safety /\ Next => Safety'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Safety,RequestVoteAction)
  <1>1. TypeOK /\ Safety /\ RequestVoteAction => Safety' BY DEF TypeOK,RequestVoteAction,RequestVote,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,UpdateTermAction)
  <1>2. TypeOK /\ Safety /\ UpdateTermAction => Safety' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv42_d848_R0_0_I0 /\ Safety /\ BecomeLeaderAction => Safety' BY DEF TypeOK,Inv42_d848_R0_0_I0,BecomeLeaderAction,BecomeLeader,Safety,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,ClientRequestAction)
  <1>4. TypeOK /\ Safety /\ ClientRequestAction => Safety' BY DEF TypeOK,ClientRequestAction,ClientRequest,Safety,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,AppendEntriesAction)
  <1>5. TypeOK /\ Safety /\ AppendEntriesAction => Safety' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Safety,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Safety /\ HandleRequestVoteRequestAction => Safety' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Safety,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Safety /\ HandleRequestVoteResponseAction => Safety' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Safety,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Safety /\ AcceptAppendEntriesRequestAppendAction => Safety' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Safety,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Safety /\ HandleAppendEntriesResponseAction => Safety' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Safety,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv42_d848_R0_0_I0
THEOREM L_2 == TypeOK /\ Inv8_8e53_R1_0_I0 /\ Inv2907_928b_R1_1_I1 /\ Inv8_8e53_R1_0_I0 /\ Inv4738_3acc_R1_1_I1 /\ Inv27_42ac_R1_1_I1 /\ Inv42_d848_R0_0_I0 /\ Next => Inv42_d848_R0_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv42_d848_R0_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv42_d848_R0_0_I0 /\ RequestVoteAction => Inv42_d848_R0_0_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv42_d848_R0_0_I0,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) \/ (~((state[VARJ] = Leader))) \/ (~(votesGranted[VARI] \in Quorum)))'
      BY DEF Inv42_d848_R0_0_I0, RequestVoteAction
    <2> QED
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv42_d848_R0_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv42_d848_R0_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv42_d848_R0_0_I0 /\ UpdateTermAction => Inv42_d848_R0_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv42_d848_R0_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv42_d848_R0_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv8_8e53_R1_0_I0 /\ Inv42_d848_R0_0_I0 /\ BecomeLeaderAction => Inv42_d848_R0_0_I0' BY DEF TypeOK,Inv8_8e53_R1_0_I0,BecomeLeaderAction,BecomeLeader,Inv42_d848_R0_0_I0
  \* (Inv42_d848_R0_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv42_d848_R0_0_I0 /\ ClientRequestAction => Inv42_d848_R0_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv42_d848_R0_0_I0
  \* (Inv42_d848_R0_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv42_d848_R0_0_I0 /\ AppendEntriesAction => Inv42_d848_R0_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv42_d848_R0_0_I0
  \* (Inv42_d848_R0_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv42_d848_R0_0_I0 /\ HandleRequestVoteRequestAction => Inv42_d848_R0_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv42_d848_R0_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv42_d848_R0_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv2907_928b_R1_1_I1 /\ Inv8_8e53_R1_0_I0 /\ Inv4738_3acc_R1_1_I1 /\ Inv27_42ac_R1_1_I1 /\ Inv42_d848_R0_0_I0 /\ HandleRequestVoteResponseAction => Inv42_d848_R0_0_I0' BY DEF TypeOK,Inv2907_928b_R1_1_I1,Inv8_8e53_R1_0_I0,Inv4738_3acc_R1_1_I1,Inv27_42ac_R1_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv42_d848_R0_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv42_d848_R0_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv42_d848_R0_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv42_d848_R0_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv42_d848_R0_0_I0
  \* (Inv42_d848_R0_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv42_d848_R0_0_I0 /\ HandleAppendEntriesResponseAction => Inv42_d848_R0_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv42_d848_R0_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv8_8e53_R1_0_I0
THEOREM L_3 == TypeOK /\ Inv0_2c32_R2_1_I1 /\ Inv27_42ac_R1_1_I1 /\ Inv8_8e53_R1_0_I0 /\ Next => Inv8_8e53_R1_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv8_8e53_R1_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv0_2c32_R2_1_I1 /\ Inv8_8e53_R1_0_I0 /\ RequestVoteAction => Inv8_8e53_R1_0_I0' BY DEF TypeOK,Inv0_2c32_R2_1_I1,RequestVoteAction,RequestVote,Inv8_8e53_R1_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv8_8e53_R1_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv8_8e53_R1_0_I0 /\ UpdateTermAction => Inv8_8e53_R1_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv8_8e53_R1_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv8_8e53_R1_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv8_8e53_R1_0_I0 /\ BecomeLeaderAction => Inv8_8e53_R1_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv8_8e53_R1_0_I0
  \* (Inv8_8e53_R1_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv8_8e53_R1_0_I0 /\ ClientRequestAction => Inv8_8e53_R1_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv8_8e53_R1_0_I0
  \* (Inv8_8e53_R1_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv8_8e53_R1_0_I0 /\ AppendEntriesAction => Inv8_8e53_R1_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv8_8e53_R1_0_I0
  \* (Inv8_8e53_R1_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv8_8e53_R1_0_I0 /\ HandleRequestVoteRequestAction => Inv8_8e53_R1_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv8_8e53_R1_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv8_8e53_R1_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv27_42ac_R1_1_I1 /\ Inv8_8e53_R1_0_I0 /\ HandleRequestVoteResponseAction => Inv8_8e53_R1_0_I0' BY DEF TypeOK,Inv27_42ac_R1_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv8_8e53_R1_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv8_8e53_R1_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv8_8e53_R1_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv8_8e53_R1_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv8_8e53_R1_0_I0
  \* (Inv8_8e53_R1_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv8_8e53_R1_0_I0 /\ HandleAppendEntriesResponseAction => Inv8_8e53_R1_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv8_8e53_R1_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv27_42ac_R1_1_I1
THEOREM L_4 == TypeOK /\ Inv12_f533_R5_2_I0 /\ Inv10_e30e_R5_0_I1 /\ Inv9_82b3_R5_1_I0 /\ Inv27_42ac_R1_1_I1 /\ Next => Inv27_42ac_R1_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv27_42ac_R1_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv12_f533_R5_2_I0 /\ Inv27_42ac_R1_1_I1 /\ RequestVoteAction => Inv27_42ac_R1_1_I1' BY DEF TypeOK,Inv12_f533_R5_2_I0,RequestVoteAction,RequestVote,Inv27_42ac_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv27_42ac_R1_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv27_42ac_R1_1_I1 /\ UpdateTermAction => Inv27_42ac_R1_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv27_42ac_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv27_42ac_R1_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv27_42ac_R1_1_I1 /\ BecomeLeaderAction => Inv27_42ac_R1_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv27_42ac_R1_1_I1
  \* (Inv27_42ac_R1_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv27_42ac_R1_1_I1 /\ ClientRequestAction => Inv27_42ac_R1_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv27_42ac_R1_1_I1
  \* (Inv27_42ac_R1_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv27_42ac_R1_1_I1 /\ AppendEntriesAction => Inv27_42ac_R1_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv27_42ac_R1_1_I1
  \* (Inv27_42ac_R1_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv10_e30e_R5_0_I1 /\ Inv27_42ac_R1_1_I1 /\ HandleRequestVoteRequestAction => Inv27_42ac_R1_1_I1' BY DEF TypeOK,Inv10_e30e_R5_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv27_42ac_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv27_42ac_R1_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv9_82b3_R5_1_I0 /\ Inv27_42ac_R1_1_I1 /\ HandleRequestVoteResponseAction => Inv27_42ac_R1_1_I1' BY DEF TypeOK,Inv9_82b3_R5_1_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv27_42ac_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv27_42ac_R1_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv27_42ac_R1_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv27_42ac_R1_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv27_42ac_R1_1_I1
  \* (Inv27_42ac_R1_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv27_42ac_R1_1_I1 /\ HandleAppendEntriesResponseAction => Inv27_42ac_R1_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv27_42ac_R1_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next



\*Inv1566_R0_1_I1 == \A VARI \in Server : \A VARJ \in Server : ~((currentTerm[VARI] > currentTerm[VARJ])) \/ (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])))
\*Inv7_R1_0_I0 == (\A s \in Server : state[s] \in {Candidate,Leader} =>  (\A t \in votesGranted[s] :  /\ currentTerm[t] = currentTerm[s] => votedFor[t] = s ))

\* Inv0_2c32_R2_1_I1_alt == \A VARI \in Server : \A VARJ \in Server : ((currentTerm[VARI] <= currentTerm[VARJ])) \/ (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])))
\* Inv10_e30e_R5_0_I1_alt == \A VARI \in Server :  (((state[VARI] # Follower))) => ((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI ))
\* Inv10_e30e_R5_0_I1_alt == \A VARI \in Server :  (((state[VARI] \in {Candidate,Leader}))) => ((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI ))
\*
\*THEOREM TypeOK /\ Inv1566_R0_1_I1 /\ Inv7_R1_0_I0 /\ RequestVoteAction => Inv7_R1_0_I0' 
\*    BY DEF TypeOK,Inv0_2c32_R2_1_I1,LastTerm,RequestVoteAction,RequestVote,Inv7_R1_0_I0,Inv1566_R0_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
\*
\*THEOREM TypeOK /\ Inv0_2c32_R2_1_I1_alt /\ Inv10_e30e_R5_0_I1_alt /\ RequestVoteAction => Inv10_e30e_R5_0_I1_alt' 
\*    BY DEF TypeOK,Inv0_2c32_R2_1_I1_alt,LastTerm,RequestVoteAction,RequestVote,Inv7_R1_0_I0,Inv10_e30e_R5_0_I1_alt,
\*    RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType


\*THEOREM Inv7_R1_0_I0 => Inv10_e30e_R5_0_I1
\*    <1> QED 
\*      <2> SUFFICES ASSUME Inv7_R1_0_I0,
\*                          NEW VARI \in Server,
\*                          state[VARI] # Follower,
\*                          NEW t \in votesGranted[VARI]
\*                   PROVE  /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI
\*        BY DEF Inv10_e30e_R5_0_I1
\*      <2>1. currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI
\*        BY DEF TypeOK,Inv0_2c32_R2_1_I1,Inv10_e30e_R5_0_I1,LastTerm,RequestVoteAction,RequestVote,Inv7_R1_0_I0,Inv1566_R0_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
\*      <2>2. QED
\*        BY <2>1

\*** Inv10_e30e_R5_0_I1
THEOREM L_5 == TypeOK /\ Inv0_2c32_R2_1_I1 /\ Inv0_2c32_R2_1_I1 /\ Inv9_3715_R8_0_I0 /\ Inv10_e30e_R5_0_I1 /\ Next => Inv10_e30e_R5_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv10_e30e_R5_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv0_2c32_R2_1_I1 /\ Inv10_e30e_R5_0_I1 /\ RequestVoteAction => Inv10_e30e_R5_0_I1' 
    BY DEF TypeOK,Inv0_2c32_R2_1_I1,LastTerm,RequestVoteAction,RequestVote,Inv10_e30e_R5_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    
  \* (Inv10_e30e_R5_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv0_2c32_R2_1_I1 /\ Inv10_e30e_R5_0_I1 /\ UpdateTermAction => Inv10_e30e_R5_0_I1' 
    BY DEF TypeOK,Inv0_2c32_R2_1_I1,UpdateTermAction,UpdateTerm,Inv10_e30e_R5_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    
  \* (Inv10_e30e_R5_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv10_e30e_R5_0_I1 /\ BecomeLeaderAction => Inv10_e30e_R5_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv10_e30e_R5_0_I1
  \* (Inv10_e30e_R5_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv10_e30e_R5_0_I1 /\ ClientRequestAction => Inv10_e30e_R5_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv10_e30e_R5_0_I1
  \* (Inv10_e30e_R5_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv10_e30e_R5_0_I1 /\ AppendEntriesAction => Inv10_e30e_R5_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv10_e30e_R5_0_I1
  \* (Inv10_e30e_R5_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv10_e30e_R5_0_I1 /\ HandleRequestVoteRequestAction => Inv10_e30e_R5_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_e30e_R5_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_e30e_R5_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv9_3715_R8_0_I0 /\ Inv10_e30e_R5_0_I1 /\ HandleRequestVoteResponseAction => Inv10_e30e_R5_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv9_3715_R8_0_I0,
                        Inv10_e30e_R5_0_I1,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server',
                        (state[VARI] # Follower)',
                        NEW t \in (votesGranted[VARI])'
                 PROVE  (/\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI)'
      BY DEF HandleRequestVoteResponseAction, Inv10_e30e_R5_0_I1
    <2>1. (currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI)'
      <3> SUFFICES ASSUME (currentTerm[t] = currentTerm[VARI])'
                   PROVE  (votedFor[t] = VARI)'
        OBVIOUS
      <3>1. CASE m.mvoteGranted /\ m.mdest # VARI
              BY <3>1, FS_Singleton, FS_Difference, FS_Subset, FS_Union, StaticQuorumsOverlap DEF TypeOK,Inv9_3715_R8_0_I0,Inv10_e30e_R5_0_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
      <3>2. CASE m.mvoteGranted /\ m.mdest = VARI
        <4>1. votedFor[t] = m.mdest
              BY <3>2, FS_Singleton, FS_Difference, FS_Subset, FS_Union, StaticQuorumsOverlap DEF TypeOK,Inv9_3715_R8_0_I0,Inv10_e30e_R5_0_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
        <4>2. QED 
                BY <3>2,<4>1, FS_Singleton, FS_Difference, FS_Subset, FS_Union, StaticQuorumsOverlap DEF TypeOK,Inv9_3715_R8_0_I0,Inv10_e30e_R5_0_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
        
      <3>3. CASE ~m.mvoteGranted
              BY <3>2, FS_Singleton, FS_Difference, FS_Subset, FS_Union, StaticQuorumsOverlap DEF TypeOK,Inv9_3715_R8_0_I0,Inv10_e30e_R5_0_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            
      <3> QED
        BY <3>1,<3>2,<3>3,FS_Singleton, FS_Difference, FS_Subset, FS_Union, StaticQuorumsOverlap DEF TypeOK,Inv9_3715_R8_0_I0,Inv10_e30e_R5_0_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
      
    <2>2. QED
      BY <2>1
  \* (Inv10_e30e_R5_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv10_e30e_R5_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv10_e30e_R5_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv10_e30e_R5_0_I1
  \* (Inv10_e30e_R5_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv10_e30e_R5_0_I1 /\ HandleAppendEntriesResponseAction => Inv10_e30e_R5_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv10_e30e_R5_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv9_3715_R8_0_I0
THEOREM L_6 == TypeOK /\ Inv12_f533_R5_2_I0 /\ Inv12_f533_R5_2_I0 /\ Inv9_3715_R8_0_I0 /\ Next => Inv9_3715_R8_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv9_3715_R8_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv12_f533_R5_2_I0 /\ Inv9_3715_R8_0_I0 /\ RequestVoteAction => Inv9_3715_R8_0_I0' BY DEF TypeOK,Inv12_f533_R5_2_I0,RequestVoteAction,RequestVote,Inv9_3715_R8_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv9_3715_R8_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv12_f533_R5_2_I0 /\ Inv9_3715_R8_0_I0 /\ UpdateTermAction => Inv9_3715_R8_0_I0' BY DEF TypeOK,Inv12_f533_R5_2_I0,UpdateTermAction,UpdateTerm,Inv9_3715_R8_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv9_3715_R8_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv9_3715_R8_0_I0 /\ BecomeLeaderAction => Inv9_3715_R8_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv9_3715_R8_0_I0
  \* (Inv9_3715_R8_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv9_3715_R8_0_I0 /\ ClientRequestAction => Inv9_3715_R8_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv9_3715_R8_0_I0
  \* (Inv9_3715_R8_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv9_3715_R8_0_I0 /\ AppendEntriesAction => Inv9_3715_R8_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv9_3715_R8_0_I0
  \* (Inv9_3715_R8_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv9_3715_R8_0_I0 /\ HandleRequestVoteRequestAction => Inv9_3715_R8_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_3715_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv9_3715_R8_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv9_3715_R8_0_I0 /\ HandleRequestVoteResponseAction => Inv9_3715_R8_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv9_3715_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv9_3715_R8_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv9_3715_R8_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv9_3715_R8_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv9_3715_R8_0_I0
  \* (Inv9_3715_R8_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv9_3715_R8_0_I0 /\ HandleAppendEntriesResponseAction => Inv9_3715_R8_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv9_3715_R8_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv12_f533_R5_2_I0
THEOREM L_7 == TypeOK /\ Inv12_f533_R5_2_I0 /\ Next => Inv12_f533_R5_2_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv12_f533_R5_2_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv12_f533_R5_2_I0 /\ RequestVoteAction => Inv12_f533_R5_2_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv12_f533_R5_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv12_f533_R5_2_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv12_f533_R5_2_I0 /\ UpdateTermAction => Inv12_f533_R5_2_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv12_f533_R5_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv12_f533_R5_2_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv12_f533_R5_2_I0 /\ BecomeLeaderAction => Inv12_f533_R5_2_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv12_f533_R5_2_I0
  \* (Inv12_f533_R5_2_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv12_f533_R5_2_I0 /\ ClientRequestAction => Inv12_f533_R5_2_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv12_f533_R5_2_I0
  \* (Inv12_f533_R5_2_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv12_f533_R5_2_I0 /\ AppendEntriesAction => Inv12_f533_R5_2_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv12_f533_R5_2_I0
  \* (Inv12_f533_R5_2_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv12_f533_R5_2_I0 /\ HandleRequestVoteRequestAction => Inv12_f533_R5_2_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv12_f533_R5_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv12_f533_R5_2_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv12_f533_R5_2_I0 /\ HandleRequestVoteResponseAction => Inv12_f533_R5_2_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv12_f533_R5_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv12_f533_R5_2_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv12_f533_R5_2_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv12_f533_R5_2_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv12_f533_R5_2_I0
  \* (Inv12_f533_R5_2_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv12_f533_R5_2_I0 /\ HandleAppendEntriesResponseAction => Inv12_f533_R5_2_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv12_f533_R5_2_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv0_2c32_R2_1_I1
THEOREM L_8 == TypeOK /\ Inv12_f533_R5_2_I0 /\ Inv0_2c32_R2_1_I1 /\ Next => Inv0_2c32_R2_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv0_2c32_R2_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv0_2c32_R2_1_I1 /\ RequestVoteAction => Inv0_2c32_R2_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv0_2c32_R2_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv0_2c32_R2_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv0_2c32_R2_1_I1 /\ UpdateTermAction => Inv0_2c32_R2_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv0_2c32_R2_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv0_2c32_R2_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv0_2c32_R2_1_I1 /\ BecomeLeaderAction => Inv0_2c32_R2_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv0_2c32_R2_1_I1
  \* (Inv0_2c32_R2_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv0_2c32_R2_1_I1 /\ ClientRequestAction => Inv0_2c32_R2_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv0_2c32_R2_1_I1
  \* (Inv0_2c32_R2_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv0_2c32_R2_1_I1 /\ AppendEntriesAction => Inv0_2c32_R2_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv0_2c32_R2_1_I1
  \* (Inv0_2c32_R2_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv0_2c32_R2_1_I1 /\ HandleRequestVoteRequestAction => Inv0_2c32_R2_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv0_2c32_R2_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_2c32_R2_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv12_f533_R5_2_I0 /\ Inv0_2c32_R2_1_I1 /\ HandleRequestVoteResponseAction => Inv0_2c32_R2_1_I1' BY DEF TypeOK,Inv12_f533_R5_2_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv0_2c32_R2_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_2c32_R2_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv0_2c32_R2_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv0_2c32_R2_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv0_2c32_R2_1_I1
  \* (Inv0_2c32_R2_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv0_2c32_R2_1_I1 /\ HandleAppendEntriesResponseAction => Inv0_2c32_R2_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv0_2c32_R2_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv9_82b3_R5_1_I0
THEOREM L_9 == TypeOK /\ Inv9_3715_R8_0_I0 /\ Inv9_82b3_R5_1_I0 /\ Next => Inv9_82b3_R5_1_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv9_82b3_R5_1_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv9_82b3_R5_1_I0 /\ RequestVoteAction => Inv9_82b3_R5_1_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv9_82b3_R5_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv9_82b3_R5_1_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv9_82b3_R5_1_I0 /\ UpdateTermAction => Inv9_82b3_R5_1_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv9_82b3_R5_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv9_82b3_R5_1_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv9_82b3_R5_1_I0 /\ BecomeLeaderAction => Inv9_82b3_R5_1_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv9_82b3_R5_1_I0
  \* (Inv9_82b3_R5_1_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv9_82b3_R5_1_I0 /\ ClientRequestAction => Inv9_82b3_R5_1_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv9_82b3_R5_1_I0
  \* (Inv9_82b3_R5_1_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv9_82b3_R5_1_I0 /\ AppendEntriesAction => Inv9_82b3_R5_1_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv9_82b3_R5_1_I0
  \* (Inv9_82b3_R5_1_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv9_3715_R8_0_I0 /\ Inv9_82b3_R5_1_I0 /\ HandleRequestVoteRequestAction => Inv9_82b3_R5_1_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv9_3715_R8_0_I0,
                        Inv9_82b3_R5_1_I0,
                        NEW m \in requestVoteRequestMsgs,
                        HandleRequestVoteRequest(m),
                        NEW mi \in requestVoteResponseMsgs', NEW mj \in requestVoteResponseMsgs',
                        (/\ mi.mterm = mj.mterm /\ mi.msource = mj.msource /\ mi.mvoteGranted /\ mj.mvoteGranted)'
                 PROVE  (mi.mdest = mj.mdest)'
      BY DEF HandleRequestVoteRequestAction, Inv9_82b3_R5_1_I0
    <2>1. CASE m.mterm # currentTerm[m.mdest]
          BY <2>1 DEF TypeOK,Inv9_3715_R8_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R5_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>2. CASE m.mterm = currentTerm[m.mdest] /\ votedFor[m.mdest] \notin {Nil, m.msource}
          BY <2>2 DEF TypeOK,Inv9_3715_R8_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R5_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>3. CASE m.mterm = currentTerm[m.mdest] /\ votedFor[m.mdest] \in {Nil, m.msource}
        <3>1. CASE m.mdest # mi.msource
            BY <2>3,<3>1 DEF TypeOK,Inv9_82b3_R5_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_3715_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         \* m is the vote request message so its dest is the one receivign the vote request.         
         <3>2. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] # mi.mterm
                BY <2>3,<3>2 DEF TypeOK,Inv9_82b3_R5_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_3715_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>3. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest # mi.msource
                BY <2>3,<3>3 DEF TypeOK,Inv9_82b3_R5_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_3715_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>4. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest = mi.msource /\ mi \in requestVoteResponseMsgs
            <4>1. currentTerm[mi.msource] = mi.mterm /\ mi.mvoteGranted
                BY <2>3,<3>4 DEF TypeOK,Inv9_82b3_R5_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_3715_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>2. votedFor[mi.msource] = mi.mdest
                BY <4>1, <2>3,<3>4 DEF TypeOK,Inv9_82b3_R5_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_3715_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. QED 
                BY <4>1, <4>2,<3>4,<2>3 DEF TypeOK,Inv9_82b3_R5_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_3715_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>5. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest = mi.msource /\ mi \notin requestVoteResponseMsgs /\ mj \notin requestVoteResponseMsgs
            <4>1. currentTerm[mi.msource] = mi.mterm /\ mi.mvoteGranted
                BY <2>3,<3>5 DEF TypeOK,Inv9_82b3_R5_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_3715_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. QED BY <4>1, <2>3,<3>5 DEF TypeOK,Inv9_82b3_R5_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_3715_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>6. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ ~mi.mvoteGranted /\ m.mdest = mi.msource /\ mi \notin requestVoteResponseMsgs /\ mj \in requestVoteResponseMsgs
            <4>2. votedFor[m.mdest] = mi.mdest
                BY <2>3,<3>6 DEF TypeOK,Inv9_82b3_R5_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_3715_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            
            <4>3. QED BY <2>3,<3>6 DEF TypeOK,Inv9_82b3_R5_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_3715_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>7. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ mi.mvoteGranted 
                                         /\ mj.mvoteGranted /\ m.mdest = mi.msource 
                                         /\ mi \notin requestVoteResponseMsgs /\ mj \in requestVoteResponseMsgs
                                         /\ votedFor[m.mdest] = Nil
            <4>2. votedFor'[m.mdest] = mi.mdest
                BY <2>3,<3>7 DEF TypeOK,Inv9_82b3_R5_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_3715_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. votedFor'[m.mdest] = mj.mdest
                BY SMTT(60), <2>3,<3>7 DEF TypeOK,Inv9_82b3_R5_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_3715_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            
            <4>4. QED BY <4>2, <4>3, <2>3,<3>7 DEF TypeOK,Inv9_82b3_R5_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_3715_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>8. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ mi.mvoteGranted 
                                         /\ mj.mvoteGranted /\ m.mdest = mi.msource 
                                         /\ mi \notin requestVoteResponseMsgs /\ mj \in requestVoteResponseMsgs
                                         /\ votedFor[m.mdest] = m.msource
            <4>2. votedFor'[m.mdest] = mi.mdest
                BY <2>3,<3>8 DEF TypeOK,Inv9_82b3_R5_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_3715_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. votedFor'[m.mdest] = m.msource
                BY <2>3,<3>8 DEF TypeOK,Inv9_82b3_R5_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_3715_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>4. mi.mdest = m.msource
                BY <2>3,<3>8 DEF TypeOK,Inv9_82b3_R5_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_3715_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>5. currentTerm[mj.msource] = mj.mterm
                BY <2>3,<3>8 DEF TypeOK,Inv9_82b3_R5_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_3715_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>6. votedFor[mj.msource] = mj.mdest
              BY <2>3,<3>8, <4>5 DEF TypeOK,Inv9_82b3_R5_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_3715_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            
            <4>7. QED BY <4>2, <4>3, <4>4,<4>6, <2>3,<3>8 
            DEF TypeOK,Inv9_82b3_R5_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_3715_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
                                            
         <3>. QED BY <3>1, <3>2, <3>3,<3>4,<3>5,<3>6,<3>7,<3>8
                     DEF TypeOK,Inv9_82b3_R5_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_3715_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         
    <2> QED
      BY <2>1, <2>2, <2>3 DEF TypeOK,Inv9_3715_R8_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R5_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
      ,TypeOK,Inv9_3715_R8_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R5_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv9_82b3_R5_1_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv9_82b3_R5_1_I0 /\ HandleRequestVoteResponseAction => Inv9_82b3_R5_1_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv9_82b3_R5_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv9_82b3_R5_1_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv9_82b3_R5_1_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv9_82b3_R5_1_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv9_82b3_R5_1_I0
  \* (Inv9_82b3_R5_1_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv9_82b3_R5_1_I0 /\ HandleAppendEntriesResponseAction => Inv9_82b3_R5_1_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv9_82b3_R5_1_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv2907_928b_R1_1_I1
THEOREM L_10 == TypeOK /\ Inv18_09bb_R3_0_I1 /\ Inv2907_928b_R1_1_I1 /\ Next => Inv2907_928b_R1_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv2907_928b_R1_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv2907_928b_R1_1_I1 /\ RequestVoteAction => Inv2907_928b_R1_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv2907_928b_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv2907_928b_R1_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv2907_928b_R1_1_I1 /\ UpdateTermAction => Inv2907_928b_R1_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv2907_928b_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv2907_928b_R1_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv2907_928b_R1_1_I1 /\ BecomeLeaderAction => Inv2907_928b_R1_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv2907_928b_R1_1_I1
  \* (Inv2907_928b_R1_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv2907_928b_R1_1_I1 /\ ClientRequestAction => Inv2907_928b_R1_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv2907_928b_R1_1_I1
  \* (Inv2907_928b_R1_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv2907_928b_R1_1_I1 /\ AppendEntriesAction => Inv2907_928b_R1_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv2907_928b_R1_1_I1
  \* (Inv2907_928b_R1_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv2907_928b_R1_1_I1 /\ HandleRequestVoteRequestAction => Inv2907_928b_R1_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv2907_928b_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv2907_928b_R1_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv18_09bb_R3_0_I1 /\ Inv2907_928b_R1_1_I1 /\ HandleRequestVoteResponseAction => Inv2907_928b_R1_1_I1' BY DEF TypeOK,Inv18_09bb_R3_0_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv2907_928b_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv2907_928b_R1_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv2907_928b_R1_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv2907_928b_R1_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv2907_928b_R1_1_I1
  \* (Inv2907_928b_R1_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv2907_928b_R1_1_I1 /\ HandleAppendEntriesResponseAction => Inv2907_928b_R1_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv2907_928b_R1_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv18_09bb_R3_0_I1
THEOREM L_11 == TypeOK /\ Inv2349_f747_R7_0_I1 /\ Inv18_09bb_R3_0_I1 /\ Next => Inv18_09bb_R3_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv18_09bb_R3_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv18_09bb_R3_0_I1 /\ RequestVoteAction => Inv18_09bb_R3_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv18_09bb_R3_0_I1,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARREQVRES \in requestVoteResponseMsgs'
                 PROVE  (~(VARREQVRES.mdest = VARI) \/ (~(votesGranted[VARI] = {})))'
      BY DEF Inv18_09bb_R3_0_I1, RequestVoteAction
    <2> QED
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv18_09bb_R3_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv18_09bb_R3_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv18_09bb_R3_0_I1 /\ UpdateTermAction => Inv18_09bb_R3_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv18_09bb_R3_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv18_09bb_R3_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv18_09bb_R3_0_I1 /\ BecomeLeaderAction => Inv18_09bb_R3_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv18_09bb_R3_0_I1
  \* (Inv18_09bb_R3_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv18_09bb_R3_0_I1 /\ ClientRequestAction => Inv18_09bb_R3_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv18_09bb_R3_0_I1
  \* (Inv18_09bb_R3_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv18_09bb_R3_0_I1 /\ AppendEntriesAction => Inv18_09bb_R3_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv18_09bb_R3_0_I1
  \* (Inv18_09bb_R3_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv2349_f747_R7_0_I1 /\ Inv18_09bb_R3_0_I1 /\ HandleRequestVoteRequestAction => Inv18_09bb_R3_0_I1' BY DEF TypeOK,Inv2349_f747_R7_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv18_09bb_R3_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv18_09bb_R3_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv18_09bb_R3_0_I1 /\ HandleRequestVoteResponseAction => Inv18_09bb_R3_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv18_09bb_R3_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv18_09bb_R3_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv18_09bb_R3_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv18_09bb_R3_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv18_09bb_R3_0_I1
  \* (Inv18_09bb_R3_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv18_09bb_R3_0_I1 /\ HandleAppendEntriesResponseAction => Inv18_09bb_R3_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv18_09bb_R3_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv2349_f747_R7_0_I1
THEOREM L_12 == TypeOK /\ Inv2349_f747_R7_0_I1 /\ Next => Inv2349_f747_R7_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv2349_f747_R7_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv2349_f747_R7_0_I1 /\ RequestVoteAction => Inv2349_f747_R7_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv2349_f747_R7_0_I1,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARJ \in Server',
                        NEW VARREQVM \in requestVoteRequestMsgs',
                        (VARREQVM.msource = VARJ)'
                 PROVE  (votesGranted[VARJ] # {})'
      BY DEF Inv2349_f747_R7_0_I1, RequestVoteAction
    <2>1. CASE VARJ = i
          BY <2>1, FS_Singleton, FS_EmptySet DEF TypeOK,RequestVoteAction,RequestVote,Inv2349_f747_R7_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LastTerm,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>2. CASE VARJ # i
          BY <2>2, FS_Singleton, FS_EmptySet DEF TypeOK,RequestVoteAction,RequestVote,Inv2349_f747_R7_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LastTerm,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType  
    <2> QED
      BY <2>1, <2>2, FS_Singleton, FS_EmptySet DEF TypeOK,RequestVoteAction,RequestVote,Inv2349_f747_R7_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LastTerm,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    
  \* (Inv2349_f747_R7_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv2349_f747_R7_0_I1 /\ UpdateTermAction => Inv2349_f747_R7_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv2349_f747_R7_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv2349_f747_R7_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv2349_f747_R7_0_I1 /\ BecomeLeaderAction => Inv2349_f747_R7_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv2349_f747_R7_0_I1
  \* (Inv2349_f747_R7_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv2349_f747_R7_0_I1 /\ ClientRequestAction => Inv2349_f747_R7_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv2349_f747_R7_0_I1
  \* (Inv2349_f747_R7_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv2349_f747_R7_0_I1 /\ AppendEntriesAction => Inv2349_f747_R7_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv2349_f747_R7_0_I1
  \* (Inv2349_f747_R7_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv2349_f747_R7_0_I1 /\ HandleRequestVoteRequestAction => Inv2349_f747_R7_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv2349_f747_R7_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv2349_f747_R7_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv2349_f747_R7_0_I1 /\ HandleRequestVoteResponseAction => Inv2349_f747_R7_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv2349_f747_R7_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv2349_f747_R7_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv2349_f747_R7_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv2349_f747_R7_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv2349_f747_R7_0_I1
  \* (Inv2349_f747_R7_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv2349_f747_R7_0_I1 /\ HandleAppendEntriesResponseAction => Inv2349_f747_R7_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv2349_f747_R7_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv4738_3acc_R1_1_I1
THEOREM L_13 == TypeOK /\ Inv4738_3acc_R1_1_I1 /\ Next => Inv4738_3acc_R1_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv4738_3acc_R1_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv4738_3acc_R1_1_I1 /\ RequestVoteAction => Inv4738_3acc_R1_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv4738_3acc_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv4738_3acc_R1_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv4738_3acc_R1_1_I1 /\ UpdateTermAction => Inv4738_3acc_R1_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv4738_3acc_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv4738_3acc_R1_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv4738_3acc_R1_1_I1 /\ BecomeLeaderAction => Inv4738_3acc_R1_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv4738_3acc_R1_1_I1
  \* (Inv4738_3acc_R1_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv4738_3acc_R1_1_I1 /\ ClientRequestAction => Inv4738_3acc_R1_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv4738_3acc_R1_1_I1
  \* (Inv4738_3acc_R1_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv4738_3acc_R1_1_I1 /\ AppendEntriesAction => Inv4738_3acc_R1_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv4738_3acc_R1_1_I1
  \* (Inv4738_3acc_R1_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv4738_3acc_R1_1_I1 /\ HandleRequestVoteRequestAction => Inv4738_3acc_R1_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv4738_3acc_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv4738_3acc_R1_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv4738_3acc_R1_1_I1 /\ HandleRequestVoteResponseAction => Inv4738_3acc_R1_1_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv4738_3acc_R1_1_I1,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server'
                 PROVE  ((votesGranted[VARI] \in Quorum) \/ (~((state[VARI] = Leader))))'
      BY DEF HandleRequestVoteResponseAction, Inv4738_3acc_R1_1_I1
    <2> QED
      BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv4738_3acc_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv4738_3acc_R1_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv4738_3acc_R1_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv4738_3acc_R1_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv4738_3acc_R1_1_I1
  \* (Inv4738_3acc_R1_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv4738_3acc_R1_1_I1 /\ HandleAppendEntriesResponseAction => Inv4738_3acc_R1_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv4738_3acc_R1_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0,A1,A2,A3,A4,A5,A6,A7
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal, H_OnePrimaryPerTerm
    <1>2. Init => Inv42_d848_R0_0_I0 BY DEF Init, Inv42_d848_R0_0_I0, IndGlobal
    <1>3. Init => Inv8_8e53_R1_0_I0 BY DEF Init, Inv8_8e53_R1_0_I0, IndGlobal
    <1>4. Init => Inv27_42ac_R1_1_I1 BY DEF Init, Inv27_42ac_R1_1_I1, IndGlobal
    <1>5. Init => Inv10_e30e_R5_0_I1 BY DEF Init, Inv10_e30e_R5_0_I1, IndGlobal
    <1>6. Init => Inv9_3715_R8_0_I0 BY DEF Init, Inv9_3715_R8_0_I0, IndGlobal
    <1>7. Init => Inv12_f533_R5_2_I0 BY DEF Init, Inv12_f533_R5_2_I0, IndGlobal
    <1>8. Init => Inv0_2c32_R2_1_I1 BY DEF Init, Inv0_2c32_R2_1_I1, IndGlobal
    <1>9. Init => Inv9_82b3_R5_1_I0 BY DEF Init, Inv9_82b3_R5_1_I0, IndGlobal
    <1>10. Init => Inv2907_928b_R1_1_I1 BY DEF Init, Inv2907_928b_R1_1_I1, IndGlobal
    <1>11. Init => Inv18_09bb_R3_0_I1 BY DEF Init, Inv18_09bb_R3_0_I1, IndGlobal
    <1>12. Init => Inv2349_f747_R7_0_I1 BY DEF Init, Inv2349_f747_R7_0_I1, IndGlobal
    <1>13. Init => Inv4738_3acc_R1_1_I1 BY DEF Init, Inv4738_3acc_R1_1_I1, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13 DEF Next, IndGlobal

====================
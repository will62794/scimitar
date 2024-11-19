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



\* Proof Graph Stats
\* ==================
\* seed: 1
\* num proof graph nodes: 8
\* num proof obligations: 72
Safety == H_OnePrimaryPerTerm
Inv31_8e53_R0_0_I1 == (\A s,t \in Server : ( /\ s # t /\ state[s] \in {Leader,Candidate} /\ state[t] \in {Leader,Candidate} /\ currentTerm[s] = currentTerm[t]) => votesGranted[s] \cap votesGranted[t] = {})
Inv1506_3acc_R0_0_I1 == \A VARI \in Server : (votesGranted[VARI] \in Quorum) \/ (~((state[VARI] = Leader)))
Inv24_42ac_R1_0_I0 == (\A s,t \in Server : \A m \in requestVoteResponseMsgs :( /\ state[s] \in {Candidate,Leader} /\ t \in votesGranted[s]) => ~(/\ m.mterm = currentTerm[s] /\ m.msource = t /\ m.mdest # s /\ m.mvoteGranted))
Inv163_6611_R1_1_I1 == \A VARI \in Server : \A VARJ \in Server : ((currentTerm[VARJ] >= currentTerm[VARI])) \/ (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])))
Inv11_e30e_R3_0_I1 == \A VARI \in Server : ((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI )) \/ (((state[VARI] = Follower)))
Inv7_f533_R3_1_I0 == \A VARREQVRES \in requestVoteResponseMsgs : (currentTerm[VARREQVRES.msource] >= VARREQVRES.mterm)
Inv7_3715_R5_0_I0 == (\A m \in requestVoteResponseMsgs : m.mtype = RequestVoteResponse =>  /\ (m.mvoteGranted /\ (currentTerm[m.msource] = m.mterm)) => votedFor[m.msource] = m.mdest)

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv31_8e53_R0_0_I1
  /\ Inv24_42ac_R1_0_I0
  /\ Inv11_e30e_R3_0_I1
  /\ Inv7_3715_R5_0_I0
  /\ Inv7_f533_R3_1_I0
  /\ Inv163_6611_R1_1_I1
  /\ Inv1506_3acc_R0_0_I1


\* mean in-degree: 1.375
\* median in-degree: 2
\* max in-degree: 2
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

USE StaticQuorumsOverlap,AddingToQuorumRemainsQuorum,QuorumsAreServerSubsets,QuorumsExistForNonEmptySets, FS_Subset

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
THEOREM L_1 == TypeOK /\ Inv31_8e53_R0_0_I1 /\ Inv1506_3acc_R0_0_I1 /\ Safety /\ Next => Safety'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Safety,RequestVoteAction)
  <1>1. TypeOK /\ Safety /\ RequestVoteAction => Safety' BY DEF TypeOK,RequestVoteAction,RequestVote,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,UpdateTermAction)
  <1>2. TypeOK /\ Safety /\ UpdateTermAction => Safety' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv31_8e53_R0_0_I1 /\ Inv1506_3acc_R0_0_I1 /\ Safety /\ BecomeLeaderAction => Safety' BY DEF TypeOK,Inv31_8e53_R0_0_I1,Inv1506_3acc_R0_0_I1,BecomeLeaderAction,BecomeLeader,Safety,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
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


\*** Inv31_8e53_R0_0_I1
THEOREM L_2 == TypeOK /\ Inv163_6611_R1_1_I1 /\ Inv24_42ac_R1_0_I0 /\ Inv31_8e53_R0_0_I1 /\ Next => Inv31_8e53_R0_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv31_8e53_R0_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv163_6611_R1_1_I1 /\ Inv31_8e53_R0_0_I1 /\ RequestVoteAction => Inv31_8e53_R0_0_I1' BY DEF TypeOK,Inv163_6611_R1_1_I1,RequestVoteAction,RequestVote,Inv31_8e53_R0_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv31_8e53_R0_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv31_8e53_R0_0_I1 /\ UpdateTermAction => Inv31_8e53_R0_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv31_8e53_R0_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv31_8e53_R0_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv31_8e53_R0_0_I1 /\ BecomeLeaderAction => Inv31_8e53_R0_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv31_8e53_R0_0_I1
  \* (Inv31_8e53_R0_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv31_8e53_R0_0_I1 /\ ClientRequestAction => Inv31_8e53_R0_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv31_8e53_R0_0_I1
  \* (Inv31_8e53_R0_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv31_8e53_R0_0_I1 /\ AppendEntriesAction => Inv31_8e53_R0_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv31_8e53_R0_0_I1
  \* (Inv31_8e53_R0_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv31_8e53_R0_0_I1 /\ HandleRequestVoteRequestAction => Inv31_8e53_R0_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv31_8e53_R0_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv31_8e53_R0_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv24_42ac_R1_0_I0 /\ Inv31_8e53_R0_0_I1 /\ HandleRequestVoteResponseAction => Inv31_8e53_R0_0_I1' BY DEF TypeOK,Inv24_42ac_R1_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv31_8e53_R0_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv31_8e53_R0_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv31_8e53_R0_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv31_8e53_R0_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv31_8e53_R0_0_I1
  \* (Inv31_8e53_R0_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv31_8e53_R0_0_I1 /\ HandleAppendEntriesResponseAction => Inv31_8e53_R0_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv31_8e53_R0_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv24_42ac_R1_0_I0
THEOREM L_3 == TypeOK /\ Inv7_f533_R3_1_I0 /\ Inv11_e30e_R3_0_I1 /\ Inv24_42ac_R1_0_I0 /\ Next => Inv24_42ac_R1_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv24_42ac_R1_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv7_f533_R3_1_I0 /\ Inv24_42ac_R1_0_I0 /\ RequestVoteAction => Inv24_42ac_R1_0_I0' BY DEF TypeOK,Inv7_f533_R3_1_I0,RequestVoteAction,RequestVote,Inv24_42ac_R1_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv24_42ac_R1_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv24_42ac_R1_0_I0 /\ UpdateTermAction => Inv24_42ac_R1_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv24_42ac_R1_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv24_42ac_R1_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv24_42ac_R1_0_I0 /\ BecomeLeaderAction => Inv24_42ac_R1_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv24_42ac_R1_0_I0
  \* (Inv24_42ac_R1_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv24_42ac_R1_0_I0 /\ ClientRequestAction => Inv24_42ac_R1_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv24_42ac_R1_0_I0
  \* (Inv24_42ac_R1_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv24_42ac_R1_0_I0 /\ AppendEntriesAction => Inv24_42ac_R1_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv24_42ac_R1_0_I0
  \* (Inv24_42ac_R1_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv11_e30e_R3_0_I1 /\ Inv24_42ac_R1_0_I0 /\ HandleRequestVoteRequestAction => Inv24_42ac_R1_0_I0' BY DEF TypeOK,Inv11_e30e_R3_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv24_42ac_R1_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv24_42ac_R1_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv24_42ac_R1_0_I0 /\ HandleRequestVoteResponseAction => Inv24_42ac_R1_0_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv24_42ac_R1_0_I0,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW s \in Server', NEW t \in Server',
                        NEW m_1 \in requestVoteResponseMsgs',
                        (/\ state[s] \in {Candidate,Leader} /\ t \in votesGranted[s])'
                 PROVE  (~(/\ m_1.mterm = currentTerm[s] /\ m_1.msource = t /\ m_1.mdest # s /\ m_1.mvoteGranted))'
      BY DEF HandleRequestVoteResponseAction, Inv24_42ac_R1_0_I0
    <2> QED
      BY FS_Subset DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv24_42ac_R1_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv24_42ac_R1_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv24_42ac_R1_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv24_42ac_R1_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv24_42ac_R1_0_I0
  \* (Inv24_42ac_R1_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv24_42ac_R1_0_I0 /\ HandleAppendEntriesResponseAction => Inv24_42ac_R1_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv24_42ac_R1_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv11_e30e_R3_0_I1
THEOREM L_4 == TypeOK /\ Inv163_6611_R1_1_I1 /\ Inv7_3715_R5_0_I0 /\ Inv11_e30e_R3_0_I1 /\ Next => Inv11_e30e_R3_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv11_e30e_R3_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv163_6611_R1_1_I1 /\ Inv11_e30e_R3_0_I1 /\ RequestVoteAction => Inv11_e30e_R3_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv163_6611_R1_1_I1,
                        Inv11_e30e_R3_0_I1,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server'
                 PROVE  (((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI )) \/ (((state[VARI] = Follower))))'
      BY DEF Inv11_e30e_R3_0_I1, RequestVoteAction
    <2> QED
      BY DEF TypeOK,Inv163_6611_R1_1_I1,RequestVoteAction,RequestVote,Inv11_e30e_R3_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv11_e30e_R3_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv11_e30e_R3_0_I1 /\ UpdateTermAction => Inv11_e30e_R3_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv11_e30e_R3_0_I1,
                        TRUE,
                        NEW m \in requestVoteRequestMsgs \cup requestVoteResponseMsgs \cup appendEntriesRequestMsgs \cup appendEntriesResponseMsgs,
                        UpdateTerm(m, m.mterm, m.mdest),
                        NEW VARI \in Server'
                 PROVE  (((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI )) \/ (((state[VARI] = Follower))))'
      BY DEF Inv11_e30e_R3_0_I1, UpdateTermAction
    <2> QED
      BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv11_e30e_R3_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv11_e30e_R3_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv11_e30e_R3_0_I1 /\ BecomeLeaderAction => Inv11_e30e_R3_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv11_e30e_R3_0_I1
  \* (Inv11_e30e_R3_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv11_e30e_R3_0_I1 /\ ClientRequestAction => Inv11_e30e_R3_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv11_e30e_R3_0_I1
  \* (Inv11_e30e_R3_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv11_e30e_R3_0_I1 /\ AppendEntriesAction => Inv11_e30e_R3_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv11_e30e_R3_0_I1
  \* (Inv11_e30e_R3_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv11_e30e_R3_0_I1 /\ HandleRequestVoteRequestAction => Inv11_e30e_R3_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv11_e30e_R3_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv11_e30e_R3_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv7_3715_R5_0_I0 /\ Inv11_e30e_R3_0_I1 /\ HandleRequestVoteResponseAction => Inv11_e30e_R3_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv7_3715_R5_0_I0,
                        Inv11_e30e_R3_0_I1,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server'
                 PROVE  (((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI )) \/ (((state[VARI] = Follower))))'
      BY DEF HandleRequestVoteResponseAction, Inv11_e30e_R3_0_I1
    <2> QED
      BY DEF TypeOK,Inv7_3715_R5_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv11_e30e_R3_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv11_e30e_R3_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv11_e30e_R3_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv11_e30e_R3_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv11_e30e_R3_0_I1
  \* (Inv11_e30e_R3_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv11_e30e_R3_0_I1 /\ HandleAppendEntriesResponseAction => Inv11_e30e_R3_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv11_e30e_R3_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv7_3715_R5_0_I0
THEOREM L_5 == TypeOK /\ Inv7_f533_R3_1_I0 /\ Inv7_f533_R3_1_I0 /\ Inv7_3715_R5_0_I0 /\ Next => Inv7_3715_R5_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv7_3715_R5_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv7_f533_R3_1_I0 /\ Inv7_3715_R5_0_I0 /\ RequestVoteAction => Inv7_3715_R5_0_I0' BY DEF TypeOK,Inv7_f533_R3_1_I0,RequestVoteAction,RequestVote,Inv7_3715_R5_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7_3715_R5_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv7_f533_R3_1_I0 /\ Inv7_3715_R5_0_I0 /\ UpdateTermAction => Inv7_3715_R5_0_I0' BY DEF TypeOK,Inv7_f533_R3_1_I0,UpdateTermAction,UpdateTerm,Inv7_3715_R5_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7_3715_R5_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv7_3715_R5_0_I0 /\ BecomeLeaderAction => Inv7_3715_R5_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv7_3715_R5_0_I0
  \* (Inv7_3715_R5_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv7_3715_R5_0_I0 /\ ClientRequestAction => Inv7_3715_R5_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv7_3715_R5_0_I0
  \* (Inv7_3715_R5_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv7_3715_R5_0_I0 /\ AppendEntriesAction => Inv7_3715_R5_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv7_3715_R5_0_I0
  \* (Inv7_3715_R5_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv7_3715_R5_0_I0 /\ HandleRequestVoteRequestAction => Inv7_3715_R5_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7_3715_R5_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv7_3715_R5_0_I0 /\ HandleRequestVoteResponseAction => Inv7_3715_R5_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv7_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7_3715_R5_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv7_3715_R5_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv7_3715_R5_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv7_3715_R5_0_I0
  \* (Inv7_3715_R5_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv7_3715_R5_0_I0 /\ HandleAppendEntriesResponseAction => Inv7_3715_R5_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv7_3715_R5_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv7_f533_R3_1_I0
THEOREM L_6 == TypeOK /\ Inv7_f533_R3_1_I0 /\ Next => Inv7_f533_R3_1_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv7_f533_R3_1_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv7_f533_R3_1_I0 /\ RequestVoteAction => Inv7_f533_R3_1_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv7_f533_R3_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7_f533_R3_1_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv7_f533_R3_1_I0 /\ UpdateTermAction => Inv7_f533_R3_1_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv7_f533_R3_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7_f533_R3_1_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv7_f533_R3_1_I0 /\ BecomeLeaderAction => Inv7_f533_R3_1_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv7_f533_R3_1_I0
  \* (Inv7_f533_R3_1_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv7_f533_R3_1_I0 /\ ClientRequestAction => Inv7_f533_R3_1_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv7_f533_R3_1_I0
  \* (Inv7_f533_R3_1_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv7_f533_R3_1_I0 /\ AppendEntriesAction => Inv7_f533_R3_1_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv7_f533_R3_1_I0
  \* (Inv7_f533_R3_1_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv7_f533_R3_1_I0 /\ HandleRequestVoteRequestAction => Inv7_f533_R3_1_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7_f533_R3_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7_f533_R3_1_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv7_f533_R3_1_I0 /\ HandleRequestVoteResponseAction => Inv7_f533_R3_1_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv7_f533_R3_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7_f533_R3_1_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv7_f533_R3_1_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv7_f533_R3_1_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv7_f533_R3_1_I0
  \* (Inv7_f533_R3_1_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv7_f533_R3_1_I0 /\ HandleAppendEntriesResponseAction => Inv7_f533_R3_1_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv7_f533_R3_1_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv163_6611_R1_1_I1
THEOREM L_7 == TypeOK /\ Inv7_f533_R3_1_I0 /\ Inv163_6611_R1_1_I1 /\ Next => Inv163_6611_R1_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv163_6611_R1_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv163_6611_R1_1_I1 /\ RequestVoteAction => Inv163_6611_R1_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv163_6611_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv163_6611_R1_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv163_6611_R1_1_I1 /\ UpdateTermAction => Inv163_6611_R1_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv163_6611_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv163_6611_R1_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv163_6611_R1_1_I1 /\ BecomeLeaderAction => Inv163_6611_R1_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv163_6611_R1_1_I1
  \* (Inv163_6611_R1_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv163_6611_R1_1_I1 /\ ClientRequestAction => Inv163_6611_R1_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv163_6611_R1_1_I1
  \* (Inv163_6611_R1_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv163_6611_R1_1_I1 /\ AppendEntriesAction => Inv163_6611_R1_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv163_6611_R1_1_I1
  \* (Inv163_6611_R1_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv163_6611_R1_1_I1 /\ HandleRequestVoteRequestAction => Inv163_6611_R1_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv163_6611_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv163_6611_R1_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv7_f533_R3_1_I0 /\ Inv163_6611_R1_1_I1 /\ HandleRequestVoteResponseAction => Inv163_6611_R1_1_I1' BY DEF TypeOK,Inv7_f533_R3_1_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv163_6611_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv163_6611_R1_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv163_6611_R1_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv163_6611_R1_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv163_6611_R1_1_I1
  \* (Inv163_6611_R1_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv163_6611_R1_1_I1 /\ HandleAppendEntriesResponseAction => Inv163_6611_R1_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv163_6611_R1_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv1506_3acc_R0_0_I1
THEOREM L_8 == TypeOK /\ Inv1506_3acc_R0_0_I1 /\ Next => Inv1506_3acc_R0_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv1506_3acc_R0_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv1506_3acc_R0_0_I1 /\ RequestVoteAction => Inv1506_3acc_R0_0_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv1506_3acc_R0_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1506_3acc_R0_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv1506_3acc_R0_0_I1 /\ UpdateTermAction => Inv1506_3acc_R0_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv1506_3acc_R0_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1506_3acc_R0_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv1506_3acc_R0_0_I1 /\ BecomeLeaderAction => Inv1506_3acc_R0_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv1506_3acc_R0_0_I1
  \* (Inv1506_3acc_R0_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv1506_3acc_R0_0_I1 /\ ClientRequestAction => Inv1506_3acc_R0_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv1506_3acc_R0_0_I1
  \* (Inv1506_3acc_R0_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv1506_3acc_R0_0_I1 /\ AppendEntriesAction => Inv1506_3acc_R0_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv1506_3acc_R0_0_I1
  \* (Inv1506_3acc_R0_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv1506_3acc_R0_0_I1 /\ HandleRequestVoteRequestAction => Inv1506_3acc_R0_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv1506_3acc_R0_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1506_3acc_R0_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv1506_3acc_R0_0_I1 /\ HandleRequestVoteResponseAction => Inv1506_3acc_R0_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv1506_3acc_R0_0_I1,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server'
                 PROVE  ((votesGranted[VARI] \in Quorum) \/ (~((state[VARI] = Leader))))'
      BY DEF HandleRequestVoteResponseAction, Inv1506_3acc_R0_0_I1
    <2> QED
      BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv1506_3acc_R0_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1506_3acc_R0_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv1506_3acc_R0_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv1506_3acc_R0_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv1506_3acc_R0_0_I1
  \* (Inv1506_3acc_R0_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv1506_3acc_R0_0_I1 /\ HandleAppendEntriesResponseAction => Inv1506_3acc_R0_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv1506_3acc_R0_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0,A1,A2,A3,A4,A5,A6,A7
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal, H_OnePrimaryPerTerm
    <1>2. Init => Inv31_8e53_R0_0_I1 BY DEF Init, Inv31_8e53_R0_0_I1, IndGlobal
    <1>3. Init => Inv24_42ac_R1_0_I0 BY DEF Init, Inv24_42ac_R1_0_I0, IndGlobal
    <1>4. Init => Inv11_e30e_R3_0_I1 BY DEF Init, Inv11_e30e_R3_0_I1, IndGlobal
    <1>5. Init => Inv7_3715_R5_0_I0 BY DEF Init, Inv7_3715_R5_0_I0, IndGlobal
    <1>6. Init => Inv7_f533_R3_1_I0 BY DEF Init, Inv7_f533_R3_1_I0, IndGlobal
    <1>7. Init => Inv163_6611_R1_1_I1 BY DEF Init, Inv163_6611_R1_1_I1, IndGlobal
    <1>8. Init => Inv1506_3acc_R0_0_I1 BY DEF Init, Inv1506_3acc_R0_0_I1, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8 DEF Next, IndGlobal

====================
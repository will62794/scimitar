--------------------------------- MODULE AsyncRaft_IndProofs_PrimaryHasEntriesItCreated_3 ---------------------------------
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
\* seed: 3
\* num proof graph nodes: 36
\* num proof obligations: 324
Safety == H_PrimaryHasEntriesItCreated
Inv32252_9e34_R0_0_I2 == \A VARI \in Server : \A VARMAEREQ \in appendEntriesRequestMsgs : \A VARLOGINDI \in LogIndices : (VARLOGINDI \in DOMAIN log[VARI] /\ log[VARI][VARLOGINDI] = currentTerm[VARI]) \/ (~(VARLOGINDI = VARMAEREQ.mprevLogIndex + 1) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI] /\ state[VARI] = Leader)))
Inv33263_295b_R0_1_I2 == \A VARI \in Server : \A VARJ \in Server : ~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(votesGranted[VARI] \in Quorum)) \/ (~(\E INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] = currentTerm[VARI]))
Inv5_404d_R0_2_I1 == \A VARI \in Server : \A VARJ \in Server : ~((state[VARI] = Leader /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) \/ (~((state[VARJ] = Leader)))
Inv44992_e200_R1_1_I2 == \A VARI \in Server : \A VARJ \in Server : \A VARMAEREQ \in appendEntriesRequestMsgs : ~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(votesGranted[VARI] \in Quorum)) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI]))
Inv11810_6aa7_R2_1_I2 == \A VARI \in Server : \A VARJ \in Server : ((state[VARJ] = Follower)) \/ (~(votesGranted[VARJ] \in Quorum)) \/ (~((state[VARI] = Leader /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])))
Inv22719_8a29_R2_2_I2 == \A VARI \in Server : \A VARJ \in Server : ~((state[VARI] = Candidate)) \/ (~(GrantedVoteSet(VARI) \in Quorum /\ votesGranted = votesGranted /\ requestVoteResponseMsgs = requestVoteResponseMsgs)) \/ (~(\E INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] = currentTerm[VARI]))
Inv34192_7f3f_R4_1_I2 == \A VARI \in Server : \A VARMAEREQ \in appendEntriesRequestMsgs : ~((state[VARI] = Candidate)) \/ (~(GrantedVoteSet(VARI) \in Quorum /\ votesGranted = votesGranted /\ requestVoteResponseMsgs = requestVoteResponseMsgs) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI])))
Inv3_8e53_R5_0_I0 == (\A s,t \in Server : ( /\ s # t /\ state[s] \in {Leader,Candidate} /\ state[t] \in {Leader,Candidate} /\ currentTerm[s] = currentTerm[t]) => votesGranted[s] \cap votesGranted[t] = {})
Inv10_928b_R5_1_I1 == \A VARI \in Server : (VARI \in votesGranted[VARI]) \/ ((votesGranted[VARI] = {}))
Inv31_3acc_R5_1_I1 == \A VARI \in Server : (votesGranted[VARI] \in Quorum) \/ (~((state[VARI] = Leader)))
Inv5_42ac_R5_1_I1 == (\A s,t \in Server : \A m \in requestVoteResponseMsgs :( /\ state[s] \in {Candidate,Leader} /\ t \in votesGranted[s]) => ~(/\ m.mterm = currentTerm[s] /\ m.msource = t /\ m.mdest # s /\ m.mvoteGranted))
Inv23620_5cd3_R6_1_I2 == \A VARI \in Server : \A VARJ \in Server : ~((state[VARI] = Leader /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) \/ (~((state[VARJ] = Candidate))) \/ (~(GrantedVoteSet(VARJ) \in Quorum /\ votesGranted = votesGranted /\ requestVoteResponseMsgs = requestVoteResponseMsgs))
Inv572_4aa6_R6_2_I1 == \A VARI \in Server : ((state[VARI] = Follower)) \/ ((votedFor[VARI] # Nil /\ VARI \in votesGranted[votedFor[VARI]]))
Inv3_c57a_R6_2_I1 == (H_LogEntryInTermImpliesSafeAtTerm /\ currentTerm = currentTerm /\ state = state /\ log = log /\ votedFor = votedFor)
Inv5_1e2e_R6_3_I1 == \A VARREQVRES \in requestVoteResponseMsgs : (currentTerm[VARREQVRES.mdest] >= VARREQVRES.mterm) \/ (~(VARREQVRES.mvoteGranted))
Inv22023_0125_R7_1_I2 == \A VARI \in Server : \A VARMAEREQ \in appendEntriesRequestMsgs : (VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] <= VARMAEREQ.mterm) \/ ((VARMAEREQ.mentries = <<>>) \/ ((votesGranted[VARI] \in Quorum)))
Inv11181_2cfb_R7_1_I2 == \A VARI \in Server : \A VARREQVRES \in requestVoteResponseMsgs : (VARI \in votesGranted[VARREQVRES.mdest]) \/ (~(VARREQVRES.mdest = VARI) \/ (~(votedFor[VARI] # Nil)))
Inv28824_2ce2_R7_1_I2 == \A VARI \in Server : \A VARJ \in Server : ~((currentTerm[VARI] > currentTerm[VARJ])) \/ (~(VARJ \in votesGranted[VARI])) \/ (~((state[VARI] = Leader /\ VARI # VARJ)))
Inv0_2c32_R8_1_I1 == \A VARI \in Server : \A VARJ \in Server : ((currentTerm[VARI] <= currentTerm[VARJ])) \/ (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])))
Inv387_09bb_R9_0_I1 == \A VARI \in Server : \A VARREQVRES \in requestVoteResponseMsgs : ~(VARREQVRES.mdest = VARI) \/ (~(votesGranted[VARI] = {}))
Inv0_e30e_R11_0_I1 == \A VARI \in Server : ((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI )) \/ (((state[VARI] = Follower)))
Inv5_82b3_R11_1_I0 == (\A mi,mj \in requestVoteResponseMsgs : (/\ mi.mterm = mj.mterm /\ mi.msource = mj.msource /\ mi.mvoteGranted /\ mj.mvoteGranted) => mi.mdest = mj.mdest)
Inv9_f533_R11_2_I0 == \A VARREQVRES \in requestVoteResponseMsgs : (currentTerm[VARREQVRES.msource] >= VARREQVRES.mterm)
Inv15_1f30_R13_0_I1 == \A VARJ \in Server : ((state[VARJ] = Follower)) \/ ((votedFor[VARJ] = VARJ))
Inv6_2014_R14_0_I0 == (H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ currentTerm = currentTerm /\ state = state /\ log = log /\ votedFor = votedFor /\ appendEntriesRequestMsgs = appendEntriesRequestMsgs)
Inv6_441b_R14_1_I1 == (H_QuorumsSafeAtTerms /\ currentTerm = currentTerm /\ state = state /\ votedFor = votedFor)
Inv23_6261_R14_1_I1 == \A VARI \in Server : ((state[VARI] = Follower)) \/ ((VARI \in votesGranted[VARI]))
Inv16213_37f1_R14_2_I2 == \A VARI \in Server : \A VARJ \in Server : \A VARREQVRES \in requestVoteResponseMsgs : (votedFor[VARREQVRES.msource] = VARREQVRES.mdest) \/ (~(VARREQVRES.mterm = currentTerm[VARI] /\ VARREQVRES.msource = VARJ /\ VARREQVRES.mdest # VARI /\ VARREQVRES.mvoteGranted)) \/ (~((currentTerm[VARI] >= currentTerm[VARJ])))
Inv3_9e78_R15_0_I0 == \A VARREQVM \in requestVoteRequestMsgs : (currentTerm[VARREQVM.msource] >= VARREQVM.mterm)
Inv23_bf9f_R16_0_I0 == \A VARI \in Server : \A VARLOGINDI \in LogIndices : ~(VARLOGINDI \in DOMAIN log[VARI] /\ log[VARI][VARLOGINDI] > currentTerm[VARI])
Inv76_9fea_R16_1_I1 == \A VARMAEREQ \in appendEntriesRequestMsgs : (VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] <= VARMAEREQ.mterm) \/ ((VARMAEREQ.mentries = <<>>))
Inv6_3122_R17_0_I1 == \A VARI \in Server : \A VARREQVM \in requestVoteRequestMsgs : (VARI \in votesGranted[VARI]) \/ (~(VARREQVM.msource = VARI))
Inv11_3715_R21_0_I0 == (\A m \in requestVoteResponseMsgs : m.mtype = RequestVoteResponse =>  /\ (m.mvoteGranted /\ (currentTerm[m.msource] = m.mterm)) => votedFor[m.msource] = m.mdest)
Inv247_73fd_R25_0_I1 == \A VARI \in Server : ((state[VARI] = Follower)) \/ ((votedFor[VARI] = VARI))
Inv12_0a54_R25_0_I1 == \A VARI \in Server : ~((commitIndex[VARI] > 0))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv32252_9e34_R0_0_I2
  /\ Inv44992_e200_R1_1_I2
  /\ Inv33263_295b_R0_1_I2
  /\ Inv11810_6aa7_R2_1_I2
  /\ Inv3_8e53_R5_0_I0
  /\ Inv5_42ac_R5_1_I1
  /\ Inv0_e30e_R11_0_I1
  /\ Inv11_3715_R21_0_I0
  /\ Inv9_f533_R11_2_I0
  /\ Inv0_2c32_R8_1_I1
  /\ Inv5_82b3_R11_1_I0
  /\ Inv10_928b_R5_1_I1
  /\ Inv387_09bb_R9_0_I1
  /\ Inv6_3122_R17_0_I1
  /\ Inv31_3acc_R5_1_I1
  /\ Inv22719_8a29_R2_2_I2
  /\ Inv34192_7f3f_R4_1_I2
  /\ Inv572_4aa6_R6_2_I1
  /\ Inv15_1f30_R13_0_I1
  /\ Inv3_c57a_R6_2_I1
  /\ Inv6_2014_R14_0_I0
  /\ Inv247_73fd_R25_0_I1
  /\ Inv12_0a54_R25_0_I1
  /\ Inv6_441b_R14_1_I1
  /\ Inv23_bf9f_R16_0_I0
  /\ Inv76_9fea_R16_1_I1
  /\ Inv23_6261_R14_1_I1
  /\ Inv16213_37f1_R14_2_I2
  /\ Inv22023_0125_R7_1_I2
  /\ Inv11181_2cfb_R7_1_I2
  /\ Inv28824_2ce2_R7_1_I2
  /\ Inv5_1e2e_R6_3_I1
  /\ Inv3_9e78_R15_0_I0
  /\ Inv23620_5cd3_R6_1_I2
  /\ Inv5_404d_R0_2_I1


\* mean in-degree: 2.1944444444444446
\* median in-degree: 2
\* max in-degree: 9
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

\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (TypeOK,RequestVoteAction)
  <1>1. TypeOK /\ TypeOK /\ RequestVoteAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ RequestVoteAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
      <3> SUFFICES ASSUME NEW i \in Server,
                          RequestVote(i)
                   PROVE  (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
        BY DEF RequestVoteAction
      <3> QED
        BY FS_Subset DEF LastTerm, TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
      
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
  <1>2. TypeOK /\ TypeOK /\ UpdateTermAction => TypeOK' 
  BY DEF TypeOK,UpdateTermAction,UpdateTerm,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (TypeOK,BecomeLeaderAction)
  <1>3. TypeOK /\ TypeOK /\ BecomeLeaderAction => TypeOK' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,TypeOK
  \* (TypeOK,ClientRequestAction)
  <1>4. TypeOK /\ TypeOK /\ ClientRequestAction => TypeOK' BY DEF TypeOK,ClientRequestAction,ClientRequest,TypeOK
  \* (TypeOK,AppendEntriesAction)
  <1>5. TypeOK /\ TypeOK /\ AppendEntriesAction => TypeOK' BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
  \* (TypeOK,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ TypeOK /\ HandleRequestVoteRequestAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ HandleRequestVoteRequestAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>2. (requestVoteResponseMsgs \in SUBSET RequestVoteResponseType)'
      BY FS_Subset DEF LastTerm, TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>3. (appendEntriesRequestMsgs \in SUBSET AppendEntriesRequestType)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>4. (appendEntriesResponseMsgs \in SUBSET AppendEntriesResponseType)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>5. (currentTerm \in [Server -> Nat])'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>6. (state       \in [Server -> {Leader, Follower, Candidate}])'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>7. (votedFor    \in [Server -> ({Nil} \cup Server)])'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>8. (votesGranted \in [Server -> (SUBSET Server)])'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>9. (nextIndex  \in [Server -> [Server -> Nat]])'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>10. (matchIndex \in [Server -> [Server -> Nat]])'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>11. (log             \in [Server -> Seq(Nat)])'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>12. (commitIndex     \in [Server -> Nat])'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>13. (\A m \in requestVoteRequestMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>14. (\A m \in requestVoteResponseMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>15. (\A m \in appendEntriesRequestMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>16. (\A m \in appendEntriesResponseMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>17. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
  \* (TypeOK,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ TypeOK /\ HandleRequestVoteResponseAction => TypeOK' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (TypeOK,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ TypeOK /\ AcceptAppendEntriesRequestAppendAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ AcceptAppendEntriesRequestAppendAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>2. (requestVoteResponseMsgs \in SUBSET RequestVoteResponseType)'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>3. (appendEntriesRequestMsgs \in SUBSET AppendEntriesRequestType)'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>4. (appendEntriesResponseMsgs \in SUBSET AppendEntriesResponseType)'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>5. (currentTerm \in [Server -> Nat])'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>6. (state       \in [Server -> {Leader, Follower, Candidate}])'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>7. (votedFor    \in [Server -> ({Nil} \cup Server)])'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>8. (votesGranted \in [Server -> (SUBSET Server)])'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>9. (nextIndex  \in [Server -> [Server -> Nat]])'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>10. (matchIndex \in [Server -> [Server -> Nat]])'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>11. (log             \in [Server -> Seq(Nat)])'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>12. (commitIndex     \in [Server -> Nat])'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>13. (\A m \in requestVoteRequestMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>14. (\A m \in requestVoteResponseMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>15. (\A m \in appendEntriesRequestMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>16. (\A m \in appendEntriesResponseMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>17. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
  \* (TypeOK,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ TypeOK /\ HandleAppendEntriesResponseAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ HandleAppendEntriesResponseAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>2. (requestVoteResponseMsgs \in SUBSET RequestVoteResponseType)'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>3. (appendEntriesRequestMsgs \in SUBSET AppendEntriesRequestType)'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>4. (appendEntriesResponseMsgs \in SUBSET AppendEntriesResponseType)'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>5. (currentTerm \in [Server -> Nat])'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>6. (state       \in [Server -> {Leader, Follower, Candidate}])'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>7. (votedFor    \in [Server -> ({Nil} \cup Server)])'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>8. (votesGranted \in [Server -> (SUBSET Server)])'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>9. (nextIndex  \in [Server -> [Server -> Nat]])'
      BY DEF Max, TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>10. (matchIndex \in [Server -> [Server -> Nat]])'
      BY DEF Max, TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>11. (log             \in [Server -> Seq(Nat)])'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>12. (commitIndex     \in [Server -> Nat])'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>13. (\A m \in requestVoteRequestMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>14. (\A m \in requestVoteResponseMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>15. (\A m \in appendEntriesRequestMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>16. (\A m \in appendEntriesResponseMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>17. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Inv33263_295b_R0_1_I2 /\ Inv5_404d_R0_2_I1 /\ Inv32252_9e34_R0_0_I2 /\ Safety /\ Next => Safety'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  <1> USE DEF H_PrimaryHasEntriesItCreated
  \* (Safety,RequestVoteAction)
  <1>1. TypeOK /\ Safety /\ RequestVoteAction => Safety' BY DEF TypeOK,RequestVoteAction,RequestVote,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  \* (Safety,UpdateTermAction)
  <1>2. TypeOK /\ Safety /\ UpdateTermAction => Safety' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  \* (Safety,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv33263_295b_R0_1_I2 /\ Safety /\ BecomeLeaderAction => Safety' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv33263_295b_R0_1_I2,
                        Safety,
                        TRUE,
                        NEW i \in Server,
                        BecomeLeader(i)
                 PROVE  Safety'
      BY DEF BecomeLeaderAction
    <2> QED
      BY DEF TypeOK,Inv33263_295b_R0_1_I2,BecomeLeaderAction,BecomeLeader,Safety,H_OnePrimaryPerTerm
  \* (Safety,ClientRequestAction)
  <1>4. TypeOK /\ Inv5_404d_R0_2_I1 /\ Safety /\ ClientRequestAction => Safety' BY DEF TypeOK,Inv5_404d_R0_2_I1,ClientRequestAction,ClientRequest,Safety,H_OnePrimaryPerTerm
  \* (Safety,AppendEntriesAction)
  <1>5. TypeOK /\ Safety /\ AppendEntriesAction => Safety' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Safety,H_OnePrimaryPerTerm
  \* (Safety,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Safety /\ HandleRequestVoteRequestAction => Safety' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Safety,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,H_OnePrimaryPerTerm
  \* (Safety,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Safety /\ HandleRequestVoteResponseAction => Safety' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Safety,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,H_OnePrimaryPerTerm
  \* (Safety,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv32252_9e34_R0_0_I2 /\ Safety /\ AcceptAppendEntriesRequestAppendAction => Safety' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv32252_9e34_R0_0_I2,
                        Safety,
                        NEW m \in appendEntriesRequestMsgs,
                        AcceptAppendEntriesRequestAppend(m)
                 PROVE  Safety'
      BY DEF AcceptAppendEntriesRequestAppendAction
    <2> QED
      BY DEF LogOk, CanAppend, TypeOK,Inv32252_9e34_R0_0_I2,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Safety,H_OnePrimaryPerTerm
  \* (Safety,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Safety /\ HandleAppendEntriesResponseAction => Safety' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Safety,H_OnePrimaryPerTerm
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv32252_9e34_R0_0_I2
THEOREM L_2 == TypeOK /\ Inv44992_e200_R1_1_I2 /\ Safety /\ Inv32252_9e34_R0_0_I2 /\ Next => Inv32252_9e34_R0_0_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv32252_9e34_R0_0_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv32252_9e34_R0_0_I2 /\ RequestVoteAction => Inv32252_9e34_R0_0_I2' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv32252_9e34_R0_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv32252_9e34_R0_0_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv32252_9e34_R0_0_I2 /\ UpdateTermAction => Inv32252_9e34_R0_0_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv32252_9e34_R0_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv32252_9e34_R0_0_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv44992_e200_R1_1_I2 /\ Inv32252_9e34_R0_0_I2 /\ BecomeLeaderAction => Inv32252_9e34_R0_0_I2' BY DEF TypeOK,Inv44992_e200_R1_1_I2,BecomeLeaderAction,BecomeLeader,Inv32252_9e34_R0_0_I2
  \* (Inv32252_9e34_R0_0_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv32252_9e34_R0_0_I2 /\ ClientRequestAction => Inv32252_9e34_R0_0_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv32252_9e34_R0_0_I2
  \* (Inv32252_9e34_R0_0_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Safety /\ Inv32252_9e34_R0_0_I2 /\ AppendEntriesAction => Inv32252_9e34_R0_0_I2' BY DEF TypeOK,Safety,AppendEntriesAction,AppendEntries,Inv32252_9e34_R0_0_I2
  \* (Inv32252_9e34_R0_0_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv32252_9e34_R0_0_I2 /\ HandleRequestVoteRequestAction => Inv32252_9e34_R0_0_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv32252_9e34_R0_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv32252_9e34_R0_0_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv32252_9e34_R0_0_I2 /\ HandleRequestVoteResponseAction => Inv32252_9e34_R0_0_I2' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv32252_9e34_R0_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv32252_9e34_R0_0_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv32252_9e34_R0_0_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv32252_9e34_R0_0_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv32252_9e34_R0_0_I2
  \* (Inv32252_9e34_R0_0_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv32252_9e34_R0_0_I2 /\ HandleAppendEntriesResponseAction => Inv32252_9e34_R0_0_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv32252_9e34_R0_0_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv44992_e200_R1_1_I2
THEOREM L_3 == TypeOK /\ Inv33263_295b_R0_1_I2 /\ Inv34192_7f3f_R4_1_I2 /\ Inv44992_e200_R1_1_I2 /\ Next => Inv44992_e200_R1_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv44992_e200_R1_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv44992_e200_R1_1_I2 /\ RequestVoteAction => Inv44992_e200_R1_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv44992_e200_R1_1_I2,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server',
                        NEW VARMAEREQ \in appendEntriesRequestMsgs'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(votesGranted[VARI] \in Quorum)) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI])))'
      BY DEF Inv44992_e200_R1_1_I2, RequestVoteAction
    <2> QED
      BY FS_Singleton, FS_Union, FS_Subset DEF TypeOK,RequestVoteAction,RequestVote,Inv44992_e200_R1_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv44992_e200_R1_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv44992_e200_R1_1_I2 /\ UpdateTermAction => Inv44992_e200_R1_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv44992_e200_R1_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv44992_e200_R1_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv44992_e200_R1_1_I2 /\ BecomeLeaderAction => Inv44992_e200_R1_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv44992_e200_R1_1_I2
  \* (Inv44992_e200_R1_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv44992_e200_R1_1_I2 /\ ClientRequestAction => Inv44992_e200_R1_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv44992_e200_R1_1_I2
  \* (Inv44992_e200_R1_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv33263_295b_R0_1_I2 /\ Inv44992_e200_R1_1_I2 /\ AppendEntriesAction => Inv44992_e200_R1_1_I2' BY DEF TypeOK,Inv33263_295b_R0_1_I2,AppendEntriesAction,AppendEntries,Inv44992_e200_R1_1_I2
  \* (Inv44992_e200_R1_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv44992_e200_R1_1_I2 /\ HandleRequestVoteRequestAction => Inv44992_e200_R1_1_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv44992_e200_R1_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv44992_e200_R1_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv34192_7f3f_R4_1_I2 /\ Inv44992_e200_R1_1_I2 /\ HandleRequestVoteResponseAction => Inv44992_e200_R1_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv34192_7f3f_R4_1_I2,
                        Inv44992_e200_R1_1_I2,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server',
                        NEW VARJ \in Server',
                        NEW VARMAEREQ \in appendEntriesRequestMsgs'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(votesGranted[VARI] \in Quorum)) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI])))'
      BY DEF HandleRequestVoteResponseAction, Inv44992_e200_R1_1_I2
    <2> QED
      BY DEF TypeOK,Inv34192_7f3f_R4_1_I2,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv44992_e200_R1_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv44992_e200_R1_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv44992_e200_R1_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv44992_e200_R1_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv44992_e200_R1_1_I2
  \* (Inv44992_e200_R1_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv44992_e200_R1_1_I2 /\ HandleAppendEntriesResponseAction => Inv44992_e200_R1_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv44992_e200_R1_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv33263_295b_R0_1_I2
THEOREM L_4 == TypeOK /\ Inv11810_6aa7_R2_1_I2 /\ Inv22719_8a29_R2_2_I2 /\ Inv44992_e200_R1_1_I2 /\ Inv33263_295b_R0_1_I2 /\ Next => Inv33263_295b_R0_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv33263_295b_R0_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv33263_295b_R0_1_I2 /\ RequestVoteAction => Inv33263_295b_R0_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv33263_295b_R0_1_I2,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(votesGranted[VARI] \in Quorum)) \/ (~(\E INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] = currentTerm[VARI])))'
      BY DEF Inv33263_295b_R0_1_I2, RequestVoteAction
    <2> QED
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv33263_295b_R0_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv33263_295b_R0_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv33263_295b_R0_1_I2 /\ UpdateTermAction => Inv33263_295b_R0_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv33263_295b_R0_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv33263_295b_R0_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv33263_295b_R0_1_I2 /\ BecomeLeaderAction => Inv33263_295b_R0_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv33263_295b_R0_1_I2
  \* (Inv33263_295b_R0_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv11810_6aa7_R2_1_I2 /\ Inv33263_295b_R0_1_I2 /\ ClientRequestAction => Inv33263_295b_R0_1_I2' BY DEF TypeOK,Inv11810_6aa7_R2_1_I2,ClientRequestAction,ClientRequest,Inv33263_295b_R0_1_I2
  \* (Inv33263_295b_R0_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv33263_295b_R0_1_I2 /\ AppendEntriesAction => Inv33263_295b_R0_1_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv33263_295b_R0_1_I2
  \* (Inv33263_295b_R0_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv33263_295b_R0_1_I2 /\ HandleRequestVoteRequestAction => Inv33263_295b_R0_1_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv33263_295b_R0_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv33263_295b_R0_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv22719_8a29_R2_2_I2 /\ Inv33263_295b_R0_1_I2 /\ HandleRequestVoteResponseAction => Inv33263_295b_R0_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv22719_8a29_R2_2_I2,
                        Inv33263_295b_R0_1_I2,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(votesGranted[VARI] \in Quorum)) \/ (~(\E INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] = currentTerm[VARI])))'
      BY DEF HandleRequestVoteResponseAction, Inv33263_295b_R0_1_I2
    <2> QED
      BY AddingToQuorumRemainsQuorum DEF TypeOK,Inv22719_8a29_R2_2_I2,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv33263_295b_R0_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv33263_295b_R0_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv44992_e200_R1_1_I2 /\ Inv33263_295b_R0_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv33263_295b_R0_1_I2' BY DEF TypeOK,Inv44992_e200_R1_1_I2,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv33263_295b_R0_1_I2
  \* (Inv33263_295b_R0_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv33263_295b_R0_1_I2 /\ HandleAppendEntriesResponseAction => Inv33263_295b_R0_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv33263_295b_R0_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv11810_6aa7_R2_1_I2
THEOREM L_5 == TypeOK /\ Inv3_8e53_R5_0_I0 /\ Inv10_928b_R5_1_I1 /\ Inv31_3acc_R5_1_I1 /\ Inv5_42ac_R5_1_I1 /\ Inv3_8e53_R5_0_I0 /\ Inv11810_6aa7_R2_1_I2 /\ Next => Inv11810_6aa7_R2_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv11810_6aa7_R2_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv11810_6aa7_R2_1_I2 /\ RequestVoteAction => Inv11810_6aa7_R2_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv11810_6aa7_R2_1_I2,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (((state[VARJ] = Follower)) \/ (~(votesGranted[VARJ] \in Quorum)) \/ (~((state[VARI] = Leader /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ]))))'
      BY DEF Inv11810_6aa7_R2_1_I2, RequestVoteAction
    <2> QED
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv11810_6aa7_R2_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv11810_6aa7_R2_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv11810_6aa7_R2_1_I2 /\ UpdateTermAction => Inv11810_6aa7_R2_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv11810_6aa7_R2_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv11810_6aa7_R2_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv3_8e53_R5_0_I0 /\ Inv11810_6aa7_R2_1_I2 /\ BecomeLeaderAction => Inv11810_6aa7_R2_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv3_8e53_R5_0_I0,
                        Inv11810_6aa7_R2_1_I2,
                        TRUE,
                        NEW i \in Server,
                        BecomeLeader(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (((state[VARJ] = Follower)) \/ (~(votesGranted[VARJ] \in Quorum)) \/ (~((state[VARI] = Leader /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ]))))'
      BY DEF BecomeLeaderAction, Inv11810_6aa7_R2_1_I2
    <2> QED
      BY DEF TypeOK,Inv3_8e53_R5_0_I0,BecomeLeaderAction,BecomeLeader,Inv11810_6aa7_R2_1_I2
  \* (Inv11810_6aa7_R2_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv11810_6aa7_R2_1_I2 /\ ClientRequestAction => Inv11810_6aa7_R2_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv11810_6aa7_R2_1_I2
  \* (Inv11810_6aa7_R2_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv11810_6aa7_R2_1_I2 /\ AppendEntriesAction => Inv11810_6aa7_R2_1_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv11810_6aa7_R2_1_I2
  \* (Inv11810_6aa7_R2_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv11810_6aa7_R2_1_I2 /\ HandleRequestVoteRequestAction => Inv11810_6aa7_R2_1_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv11810_6aa7_R2_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv11810_6aa7_R2_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv10_928b_R5_1_I1 /\ Inv31_3acc_R5_1_I1 /\ Inv5_42ac_R5_1_I1 /\ Inv3_8e53_R5_0_I0 /\ Inv11810_6aa7_R2_1_I2 /\ HandleRequestVoteResponseAction => Inv11810_6aa7_R2_1_I2' BY DEF TypeOK,Inv10_928b_R5_1_I1,Inv31_3acc_R5_1_I1,Inv5_42ac_R5_1_I1,Inv3_8e53_R5_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv11810_6aa7_R2_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv11810_6aa7_R2_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv11810_6aa7_R2_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv11810_6aa7_R2_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv11810_6aa7_R2_1_I2
  \* (Inv11810_6aa7_R2_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv11810_6aa7_R2_1_I2 /\ HandleAppendEntriesResponseAction => Inv11810_6aa7_R2_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv11810_6aa7_R2_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv3_8e53_R5_0_I0
THEOREM L_6 == TypeOK /\ Inv0_2c32_R8_1_I1 /\ Inv5_42ac_R5_1_I1 /\ Inv3_8e53_R5_0_I0 /\ Next => Inv3_8e53_R5_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv3_8e53_R5_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv0_2c32_R8_1_I1 /\ Inv3_8e53_R5_0_I0 /\ RequestVoteAction => Inv3_8e53_R5_0_I0' BY DEF TypeOK,Inv0_2c32_R8_1_I1,RequestVoteAction,RequestVote,Inv3_8e53_R5_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv3_8e53_R5_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv3_8e53_R5_0_I0 /\ UpdateTermAction => Inv3_8e53_R5_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv3_8e53_R5_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv3_8e53_R5_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv3_8e53_R5_0_I0 /\ BecomeLeaderAction => Inv3_8e53_R5_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv3_8e53_R5_0_I0
  \* (Inv3_8e53_R5_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv3_8e53_R5_0_I0 /\ ClientRequestAction => Inv3_8e53_R5_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv3_8e53_R5_0_I0
  \* (Inv3_8e53_R5_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv3_8e53_R5_0_I0 /\ AppendEntriesAction => Inv3_8e53_R5_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv3_8e53_R5_0_I0
  \* (Inv3_8e53_R5_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv3_8e53_R5_0_I0 /\ HandleRequestVoteRequestAction => Inv3_8e53_R5_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_8e53_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv3_8e53_R5_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv5_42ac_R5_1_I1 /\ Inv3_8e53_R5_0_I0 /\ HandleRequestVoteResponseAction => Inv3_8e53_R5_0_I0' BY DEF TypeOK,Inv5_42ac_R5_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv3_8e53_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv3_8e53_R5_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv3_8e53_R5_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv3_8e53_R5_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv3_8e53_R5_0_I0
  \* (Inv3_8e53_R5_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv3_8e53_R5_0_I0 /\ HandleAppendEntriesResponseAction => Inv3_8e53_R5_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv3_8e53_R5_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv5_42ac_R5_1_I1
THEOREM L_7 == TypeOK /\ Inv9_f533_R11_2_I0 /\ Inv0_e30e_R11_0_I1 /\ Inv5_82b3_R11_1_I0 /\ Inv5_42ac_R5_1_I1 /\ Next => Inv5_42ac_R5_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv5_42ac_R5_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv9_f533_R11_2_I0 /\ Inv5_42ac_R5_1_I1 /\ RequestVoteAction => Inv5_42ac_R5_1_I1' BY DEF TypeOK,Inv9_f533_R11_2_I0,RequestVoteAction,RequestVote,Inv5_42ac_R5_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5_42ac_R5_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv5_42ac_R5_1_I1 /\ UpdateTermAction => Inv5_42ac_R5_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv5_42ac_R5_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5_42ac_R5_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv5_42ac_R5_1_I1 /\ BecomeLeaderAction => Inv5_42ac_R5_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv5_42ac_R5_1_I1
  \* (Inv5_42ac_R5_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv5_42ac_R5_1_I1 /\ ClientRequestAction => Inv5_42ac_R5_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv5_42ac_R5_1_I1
  \* (Inv5_42ac_R5_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv5_42ac_R5_1_I1 /\ AppendEntriesAction => Inv5_42ac_R5_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv5_42ac_R5_1_I1
  \* (Inv5_42ac_R5_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv0_e30e_R11_0_I1 /\ Inv5_42ac_R5_1_I1 /\ HandleRequestVoteRequestAction => Inv5_42ac_R5_1_I1' BY DEF TypeOK,Inv0_e30e_R11_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_42ac_R5_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5_42ac_R5_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv5_82b3_R11_1_I0 /\ Inv5_42ac_R5_1_I1 /\ HandleRequestVoteResponseAction => Inv5_42ac_R5_1_I1' BY DEF TypeOK,Inv5_82b3_R11_1_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv5_42ac_R5_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5_42ac_R5_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv5_42ac_R5_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv5_42ac_R5_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv5_42ac_R5_1_I1
  \* (Inv5_42ac_R5_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv5_42ac_R5_1_I1 /\ HandleAppendEntriesResponseAction => Inv5_42ac_R5_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv5_42ac_R5_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv0_e30e_R11_0_I1
THEOREM L_8 == TypeOK /\ Inv0_2c32_R8_1_I1 /\ Inv0_2c32_R8_1_I1 /\ Inv11_3715_R21_0_I0 /\ Inv0_e30e_R11_0_I1 /\ Next => Inv0_e30e_R11_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv0_e30e_R11_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv0_2c32_R8_1_I1 /\ Inv0_e30e_R11_0_I1 /\ RequestVoteAction => Inv0_e30e_R11_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv0_2c32_R8_1_I1,
                        Inv0_e30e_R11_0_I1,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server'
                 PROVE  (((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI )) \/ (((state[VARI] = Follower))))'
      BY DEF Inv0_e30e_R11_0_I1, RequestVoteAction
    <2> QED
      BY DEF TypeOK,Inv0_2c32_R8_1_I1,RequestVoteAction,RequestVote,Inv0_e30e_R11_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv0_e30e_R11_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv0_2c32_R8_1_I1 /\ Inv0_e30e_R11_0_I1 /\ UpdateTermAction => Inv0_e30e_R11_0_I1' BY DEF TypeOK,Inv0_2c32_R8_1_I1,UpdateTermAction,UpdateTerm,Inv0_e30e_R11_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv0_e30e_R11_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv0_e30e_R11_0_I1 /\ BecomeLeaderAction => Inv0_e30e_R11_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv0_e30e_R11_0_I1
  \* (Inv0_e30e_R11_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv0_e30e_R11_0_I1 /\ ClientRequestAction => Inv0_e30e_R11_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv0_e30e_R11_0_I1
  \* (Inv0_e30e_R11_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv0_e30e_R11_0_I1 /\ AppendEntriesAction => Inv0_e30e_R11_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv0_e30e_R11_0_I1
  \* (Inv0_e30e_R11_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv0_e30e_R11_0_I1 /\ HandleRequestVoteRequestAction => Inv0_e30e_R11_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv0_e30e_R11_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_e30e_R11_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv11_3715_R21_0_I0 /\ Inv0_e30e_R11_0_I1 /\ HandleRequestVoteResponseAction => Inv0_e30e_R11_0_I1' BY DEF TypeOK,Inv11_3715_R21_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv0_e30e_R11_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_e30e_R11_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv0_e30e_R11_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv0_e30e_R11_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv0_e30e_R11_0_I1
  \* (Inv0_e30e_R11_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv0_e30e_R11_0_I1 /\ HandleAppendEntriesResponseAction => Inv0_e30e_R11_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv0_e30e_R11_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv11_3715_R21_0_I0
THEOREM L_9 == TypeOK /\ Inv9_f533_R11_2_I0 /\ Inv9_f533_R11_2_I0 /\ Inv11_3715_R21_0_I0 /\ Next => Inv11_3715_R21_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv11_3715_R21_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv9_f533_R11_2_I0 /\ Inv11_3715_R21_0_I0 /\ RequestVoteAction => Inv11_3715_R21_0_I0' BY DEF TypeOK,Inv9_f533_R11_2_I0,RequestVoteAction,RequestVote,Inv11_3715_R21_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv11_3715_R21_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv9_f533_R11_2_I0 /\ Inv11_3715_R21_0_I0 /\ UpdateTermAction => Inv11_3715_R21_0_I0' BY DEF TypeOK,Inv9_f533_R11_2_I0,UpdateTermAction,UpdateTerm,Inv11_3715_R21_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv11_3715_R21_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv11_3715_R21_0_I0 /\ BecomeLeaderAction => Inv11_3715_R21_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv11_3715_R21_0_I0
  \* (Inv11_3715_R21_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv11_3715_R21_0_I0 /\ ClientRequestAction => Inv11_3715_R21_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv11_3715_R21_0_I0
  \* (Inv11_3715_R21_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv11_3715_R21_0_I0 /\ AppendEntriesAction => Inv11_3715_R21_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv11_3715_R21_0_I0
  \* (Inv11_3715_R21_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv11_3715_R21_0_I0 /\ HandleRequestVoteRequestAction => Inv11_3715_R21_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv11_3715_R21_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv11_3715_R21_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv11_3715_R21_0_I0 /\ HandleRequestVoteResponseAction => Inv11_3715_R21_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv11_3715_R21_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv11_3715_R21_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv11_3715_R21_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv11_3715_R21_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv11_3715_R21_0_I0
  \* (Inv11_3715_R21_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv11_3715_R21_0_I0 /\ HandleAppendEntriesResponseAction => Inv11_3715_R21_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv11_3715_R21_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv9_f533_R11_2_I0
THEOREM L_10 == TypeOK /\ Inv9_f533_R11_2_I0 /\ Next => Inv9_f533_R11_2_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv9_f533_R11_2_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv9_f533_R11_2_I0 /\ RequestVoteAction => Inv9_f533_R11_2_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv9_f533_R11_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv9_f533_R11_2_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv9_f533_R11_2_I0 /\ UpdateTermAction => Inv9_f533_R11_2_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv9_f533_R11_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv9_f533_R11_2_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv9_f533_R11_2_I0 /\ BecomeLeaderAction => Inv9_f533_R11_2_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv9_f533_R11_2_I0
  \* (Inv9_f533_R11_2_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv9_f533_R11_2_I0 /\ ClientRequestAction => Inv9_f533_R11_2_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv9_f533_R11_2_I0
  \* (Inv9_f533_R11_2_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv9_f533_R11_2_I0 /\ AppendEntriesAction => Inv9_f533_R11_2_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv9_f533_R11_2_I0
  \* (Inv9_f533_R11_2_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv9_f533_R11_2_I0 /\ HandleRequestVoteRequestAction => Inv9_f533_R11_2_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_f533_R11_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv9_f533_R11_2_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv9_f533_R11_2_I0 /\ HandleRequestVoteResponseAction => Inv9_f533_R11_2_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv9_f533_R11_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv9_f533_R11_2_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv9_f533_R11_2_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv9_f533_R11_2_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv9_f533_R11_2_I0
  \* (Inv9_f533_R11_2_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv9_f533_R11_2_I0 /\ HandleAppendEntriesResponseAction => Inv9_f533_R11_2_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv9_f533_R11_2_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv0_2c32_R8_1_I1
THEOREM L_11 == TypeOK /\ Inv9_f533_R11_2_I0 /\ Inv0_2c32_R8_1_I1 /\ Next => Inv0_2c32_R8_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv0_2c32_R8_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv0_2c32_R8_1_I1 /\ RequestVoteAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv0_2c32_R8_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv0_2c32_R8_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv0_2c32_R8_1_I1 /\ UpdateTermAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv0_2c32_R8_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv0_2c32_R8_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv0_2c32_R8_1_I1 /\ BecomeLeaderAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv0_2c32_R8_1_I1
  \* (Inv0_2c32_R8_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv0_2c32_R8_1_I1 /\ ClientRequestAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv0_2c32_R8_1_I1
  \* (Inv0_2c32_R8_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv0_2c32_R8_1_I1 /\ AppendEntriesAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv0_2c32_R8_1_I1
  \* (Inv0_2c32_R8_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv0_2c32_R8_1_I1 /\ HandleRequestVoteRequestAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv0_2c32_R8_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_2c32_R8_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv9_f533_R11_2_I0 /\ Inv0_2c32_R8_1_I1 /\ HandleRequestVoteResponseAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,Inv9_f533_R11_2_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv0_2c32_R8_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_2c32_R8_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv0_2c32_R8_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv0_2c32_R8_1_I1
  \* (Inv0_2c32_R8_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv0_2c32_R8_1_I1 /\ HandleAppendEntriesResponseAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv0_2c32_R8_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv5_82b3_R11_1_I0
THEOREM L_12 == TypeOK /\ Inv11_3715_R21_0_I0 /\ Inv5_82b3_R11_1_I0 /\ Next => Inv5_82b3_R11_1_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv5_82b3_R11_1_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv5_82b3_R11_1_I0 /\ RequestVoteAction => Inv5_82b3_R11_1_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv5_82b3_R11_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5_82b3_R11_1_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv5_82b3_R11_1_I0 /\ UpdateTermAction => Inv5_82b3_R11_1_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv5_82b3_R11_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5_82b3_R11_1_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv5_82b3_R11_1_I0 /\ BecomeLeaderAction => Inv5_82b3_R11_1_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv5_82b3_R11_1_I0
  \* (Inv5_82b3_R11_1_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv5_82b3_R11_1_I0 /\ ClientRequestAction => Inv5_82b3_R11_1_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv5_82b3_R11_1_I0
  \* (Inv5_82b3_R11_1_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv5_82b3_R11_1_I0 /\ AppendEntriesAction => Inv5_82b3_R11_1_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv5_82b3_R11_1_I0
  \* (Inv5_82b3_R11_1_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv11_3715_R21_0_I0 /\ Inv5_82b3_R11_1_I0 /\ HandleRequestVoteRequestAction => Inv5_82b3_R11_1_I0' BY DEF TypeOK,Inv11_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_82b3_R11_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5_82b3_R11_1_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv5_82b3_R11_1_I0 /\ HandleRequestVoteResponseAction => Inv5_82b3_R11_1_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv5_82b3_R11_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5_82b3_R11_1_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv5_82b3_R11_1_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv5_82b3_R11_1_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv5_82b3_R11_1_I0
  \* (Inv5_82b3_R11_1_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv5_82b3_R11_1_I0 /\ HandleAppendEntriesResponseAction => Inv5_82b3_R11_1_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv5_82b3_R11_1_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv10_928b_R5_1_I1
THEOREM L_13 == TypeOK /\ Inv387_09bb_R9_0_I1 /\ Inv10_928b_R5_1_I1 /\ Next => Inv10_928b_R5_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv10_928b_R5_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv10_928b_R5_1_I1 /\ RequestVoteAction => Inv10_928b_R5_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv10_928b_R5_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10_928b_R5_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv10_928b_R5_1_I1 /\ UpdateTermAction => Inv10_928b_R5_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv10_928b_R5_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10_928b_R5_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv10_928b_R5_1_I1 /\ BecomeLeaderAction => Inv10_928b_R5_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv10_928b_R5_1_I1
  \* (Inv10_928b_R5_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv10_928b_R5_1_I1 /\ ClientRequestAction => Inv10_928b_R5_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv10_928b_R5_1_I1
  \* (Inv10_928b_R5_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv10_928b_R5_1_I1 /\ AppendEntriesAction => Inv10_928b_R5_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv10_928b_R5_1_I1
  \* (Inv10_928b_R5_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv10_928b_R5_1_I1 /\ HandleRequestVoteRequestAction => Inv10_928b_R5_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_928b_R5_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_928b_R5_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv387_09bb_R9_0_I1 /\ Inv10_928b_R5_1_I1 /\ HandleRequestVoteResponseAction => Inv10_928b_R5_1_I1' BY DEF TypeOK,Inv387_09bb_R9_0_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv10_928b_R5_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_928b_R5_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv10_928b_R5_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv10_928b_R5_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv10_928b_R5_1_I1
  \* (Inv10_928b_R5_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv10_928b_R5_1_I1 /\ HandleAppendEntriesResponseAction => Inv10_928b_R5_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv10_928b_R5_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv387_09bb_R9_0_I1
THEOREM L_14 == TypeOK /\ Inv6_3122_R17_0_I1 /\ Inv387_09bb_R9_0_I1 /\ Next => Inv387_09bb_R9_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv387_09bb_R9_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv387_09bb_R9_0_I1 /\ RequestVoteAction => Inv387_09bb_R9_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv387_09bb_R9_0_I1,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARREQVRES \in requestVoteResponseMsgs'
                 PROVE  (~(VARREQVRES.mdest = VARI) \/ (~(votesGranted[VARI] = {})))'
      BY DEF Inv387_09bb_R9_0_I1, RequestVoteAction
    <2> QED
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv387_09bb_R9_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv387_09bb_R9_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv387_09bb_R9_0_I1 /\ UpdateTermAction => Inv387_09bb_R9_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv387_09bb_R9_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv387_09bb_R9_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv387_09bb_R9_0_I1 /\ BecomeLeaderAction => Inv387_09bb_R9_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv387_09bb_R9_0_I1
  \* (Inv387_09bb_R9_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv387_09bb_R9_0_I1 /\ ClientRequestAction => Inv387_09bb_R9_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv387_09bb_R9_0_I1
  \* (Inv387_09bb_R9_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv387_09bb_R9_0_I1 /\ AppendEntriesAction => Inv387_09bb_R9_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv387_09bb_R9_0_I1
  \* (Inv387_09bb_R9_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv6_3122_R17_0_I1 /\ Inv387_09bb_R9_0_I1 /\ HandleRequestVoteRequestAction => Inv387_09bb_R9_0_I1' BY DEF TypeOK,Inv6_3122_R17_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv387_09bb_R9_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv387_09bb_R9_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv387_09bb_R9_0_I1 /\ HandleRequestVoteResponseAction => Inv387_09bb_R9_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv387_09bb_R9_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv387_09bb_R9_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv387_09bb_R9_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv387_09bb_R9_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv387_09bb_R9_0_I1
  \* (Inv387_09bb_R9_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv387_09bb_R9_0_I1 /\ HandleAppendEntriesResponseAction => Inv387_09bb_R9_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv387_09bb_R9_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv6_3122_R17_0_I1
THEOREM L_15 == TypeOK /\ Inv6_3122_R17_0_I1 /\ Next => Inv6_3122_R17_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv6_3122_R17_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv6_3122_R17_0_I1 /\ RequestVoteAction => Inv6_3122_R17_0_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv6_3122_R17_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6_3122_R17_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv6_3122_R17_0_I1 /\ UpdateTermAction => Inv6_3122_R17_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv6_3122_R17_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6_3122_R17_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv6_3122_R17_0_I1 /\ BecomeLeaderAction => Inv6_3122_R17_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv6_3122_R17_0_I1
  \* (Inv6_3122_R17_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv6_3122_R17_0_I1 /\ ClientRequestAction => Inv6_3122_R17_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv6_3122_R17_0_I1
  \* (Inv6_3122_R17_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv6_3122_R17_0_I1 /\ AppendEntriesAction => Inv6_3122_R17_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv6_3122_R17_0_I1
  \* (Inv6_3122_R17_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv6_3122_R17_0_I1 /\ HandleRequestVoteRequestAction => Inv6_3122_R17_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv6_3122_R17_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6_3122_R17_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv6_3122_R17_0_I1 /\ HandleRequestVoteResponseAction => Inv6_3122_R17_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv6_3122_R17_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6_3122_R17_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv6_3122_R17_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv6_3122_R17_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv6_3122_R17_0_I1
  \* (Inv6_3122_R17_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv6_3122_R17_0_I1 /\ HandleAppendEntriesResponseAction => Inv6_3122_R17_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv6_3122_R17_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv31_3acc_R5_1_I1
THEOREM L_16 == TypeOK /\ Inv31_3acc_R5_1_I1 /\ Next => Inv31_3acc_R5_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv31_3acc_R5_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv31_3acc_R5_1_I1 /\ RequestVoteAction => Inv31_3acc_R5_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv31_3acc_R5_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv31_3acc_R5_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv31_3acc_R5_1_I1 /\ UpdateTermAction => Inv31_3acc_R5_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv31_3acc_R5_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv31_3acc_R5_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv31_3acc_R5_1_I1 /\ BecomeLeaderAction => Inv31_3acc_R5_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv31_3acc_R5_1_I1
  \* (Inv31_3acc_R5_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv31_3acc_R5_1_I1 /\ ClientRequestAction => Inv31_3acc_R5_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv31_3acc_R5_1_I1
  \* (Inv31_3acc_R5_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv31_3acc_R5_1_I1 /\ AppendEntriesAction => Inv31_3acc_R5_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv31_3acc_R5_1_I1
  \* (Inv31_3acc_R5_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv31_3acc_R5_1_I1 /\ HandleRequestVoteRequestAction => Inv31_3acc_R5_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv31_3acc_R5_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv31_3acc_R5_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv31_3acc_R5_1_I1 /\ HandleRequestVoteResponseAction => Inv31_3acc_R5_1_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv31_3acc_R5_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv31_3acc_R5_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv31_3acc_R5_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv31_3acc_R5_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv31_3acc_R5_1_I1
  \* (Inv31_3acc_R5_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv31_3acc_R5_1_I1 /\ HandleAppendEntriesResponseAction => Inv31_3acc_R5_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv31_3acc_R5_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv22719_8a29_R2_2_I2
THEOREM L_17 == TypeOK /\ Inv5_1e2e_R6_3_I1 /\ Inv23620_5cd3_R6_1_I2 /\ Inv572_4aa6_R6_2_I1 /\ Inv3_c57a_R6_2_I1 /\ Inv10_928b_R5_1_I1 /\ Inv34192_7f3f_R4_1_I2 /\ Inv22719_8a29_R2_2_I2 /\ Next => Inv22719_8a29_R2_2_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF GrantedVoteSet
  \* (Inv22719_8a29_R2_2_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv5_1e2e_R6_3_I1 /\ Inv22719_8a29_R2_2_I2 /\ RequestVoteAction => Inv22719_8a29_R2_2_I2' BY DEF TypeOK,Inv5_1e2e_R6_3_I1,RequestVoteAction,RequestVote,Inv22719_8a29_R2_2_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv22719_8a29_R2_2_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv22719_8a29_R2_2_I2 /\ UpdateTermAction => Inv22719_8a29_R2_2_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv22719_8a29_R2_2_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv22719_8a29_R2_2_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv22719_8a29_R2_2_I2 /\ BecomeLeaderAction => Inv22719_8a29_R2_2_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv22719_8a29_R2_2_I2
  \* (Inv22719_8a29_R2_2_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv23620_5cd3_R6_1_I2 /\ Inv22719_8a29_R2_2_I2 /\ ClientRequestAction => Inv22719_8a29_R2_2_I2' BY DEF TypeOK,Inv23620_5cd3_R6_1_I2,ClientRequestAction,ClientRequest,Inv22719_8a29_R2_2_I2
  \* (Inv22719_8a29_R2_2_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv22719_8a29_R2_2_I2 /\ AppendEntriesAction => Inv22719_8a29_R2_2_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv22719_8a29_R2_2_I2
  \* (Inv22719_8a29_R2_2_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv572_4aa6_R6_2_I1 /\ Inv3_c57a_R6_2_I1 /\ Inv10_928b_R5_1_I1 /\ Inv22719_8a29_R2_2_I2 /\ HandleRequestVoteRequestAction => Inv22719_8a29_R2_2_I2' BY DEF TypeOK,Inv572_4aa6_R6_2_I1,Inv3_c57a_R6_2_I1,Inv10_928b_R5_1_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv22719_8a29_R2_2_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv22719_8a29_R2_2_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv22719_8a29_R2_2_I2 /\ HandleRequestVoteResponseAction => Inv22719_8a29_R2_2_I2' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv22719_8a29_R2_2_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv22719_8a29_R2_2_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv34192_7f3f_R4_1_I2 /\ Inv22719_8a29_R2_2_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv22719_8a29_R2_2_I2' BY DEF TypeOK,Inv34192_7f3f_R4_1_I2,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv22719_8a29_R2_2_I2
  \* (Inv22719_8a29_R2_2_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv22719_8a29_R2_2_I2 /\ HandleAppendEntriesResponseAction => Inv22719_8a29_R2_2_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv22719_8a29_R2_2_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv34192_7f3f_R4_1_I2
THEOREM L_18 == TypeOK /\ Inv5_1e2e_R6_3_I1 /\ Inv22719_8a29_R2_2_I2 /\ Inv572_4aa6_R6_2_I1 /\ Inv3_c57a_R6_2_I1 /\ Inv22023_0125_R7_1_I2 /\ Inv11181_2cfb_R7_1_I2 /\ Inv28824_2ce2_R7_1_I2 /\ Inv34192_7f3f_R4_1_I2 /\ Next => Inv34192_7f3f_R4_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF GrantedVoteSet
  \* (Inv34192_7f3f_R4_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv5_1e2e_R6_3_I1 /\ Inv34192_7f3f_R4_1_I2 /\ RequestVoteAction => Inv34192_7f3f_R4_1_I2' BY DEF TypeOK,Inv5_1e2e_R6_3_I1,RequestVoteAction,RequestVote,Inv34192_7f3f_R4_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv34192_7f3f_R4_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv34192_7f3f_R4_1_I2 /\ UpdateTermAction => Inv34192_7f3f_R4_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv34192_7f3f_R4_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv34192_7f3f_R4_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv34192_7f3f_R4_1_I2 /\ BecomeLeaderAction => Inv34192_7f3f_R4_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv34192_7f3f_R4_1_I2
  \* (Inv34192_7f3f_R4_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv34192_7f3f_R4_1_I2 /\ ClientRequestAction => Inv34192_7f3f_R4_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv34192_7f3f_R4_1_I2
  \* (Inv34192_7f3f_R4_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv22719_8a29_R2_2_I2 /\ Inv34192_7f3f_R4_1_I2 /\ AppendEntriesAction => Inv34192_7f3f_R4_1_I2' BY DEF TypeOK,Inv22719_8a29_R2_2_I2,AppendEntriesAction,AppendEntries,Inv34192_7f3f_R4_1_I2
  \* (Inv34192_7f3f_R4_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv572_4aa6_R6_2_I1 /\ Inv3_c57a_R6_2_I1 /\ Inv22023_0125_R7_1_I2 /\ Inv11181_2cfb_R7_1_I2 /\ Inv28824_2ce2_R7_1_I2 /\ Inv34192_7f3f_R4_1_I2 /\ HandleRequestVoteRequestAction => Inv34192_7f3f_R4_1_I2' BY DEF TypeOK,Inv572_4aa6_R6_2_I1,Inv3_c57a_R6_2_I1,Inv22023_0125_R7_1_I2,Inv11181_2cfb_R7_1_I2,Inv28824_2ce2_R7_1_I2,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv34192_7f3f_R4_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv34192_7f3f_R4_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv34192_7f3f_R4_1_I2 /\ HandleRequestVoteResponseAction => Inv34192_7f3f_R4_1_I2' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv34192_7f3f_R4_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv34192_7f3f_R4_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv34192_7f3f_R4_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv34192_7f3f_R4_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv34192_7f3f_R4_1_I2
  \* (Inv34192_7f3f_R4_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv34192_7f3f_R4_1_I2 /\ HandleAppendEntriesResponseAction => Inv34192_7f3f_R4_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv34192_7f3f_R4_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv572_4aa6_R6_2_I1
THEOREM L_19 == TypeOK /\ Inv15_1f30_R13_0_I1 /\ Inv572_4aa6_R6_2_I1 /\ Next => Inv572_4aa6_R6_2_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv572_4aa6_R6_2_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv15_1f30_R13_0_I1 /\ Inv572_4aa6_R6_2_I1 /\ RequestVoteAction => Inv572_4aa6_R6_2_I1' BY DEF TypeOK,Inv15_1f30_R13_0_I1,RequestVoteAction,RequestVote,Inv572_4aa6_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv572_4aa6_R6_2_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv572_4aa6_R6_2_I1 /\ UpdateTermAction => Inv572_4aa6_R6_2_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv572_4aa6_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv572_4aa6_R6_2_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv572_4aa6_R6_2_I1 /\ BecomeLeaderAction => Inv572_4aa6_R6_2_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv572_4aa6_R6_2_I1
  \* (Inv572_4aa6_R6_2_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv572_4aa6_R6_2_I1 /\ ClientRequestAction => Inv572_4aa6_R6_2_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv572_4aa6_R6_2_I1
  \* (Inv572_4aa6_R6_2_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv572_4aa6_R6_2_I1 /\ AppendEntriesAction => Inv572_4aa6_R6_2_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv572_4aa6_R6_2_I1
  \* (Inv572_4aa6_R6_2_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv572_4aa6_R6_2_I1 /\ HandleRequestVoteRequestAction => Inv572_4aa6_R6_2_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv572_4aa6_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv572_4aa6_R6_2_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv572_4aa6_R6_2_I1 /\ HandleRequestVoteResponseAction => Inv572_4aa6_R6_2_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv572_4aa6_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv572_4aa6_R6_2_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv572_4aa6_R6_2_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv572_4aa6_R6_2_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv572_4aa6_R6_2_I1
  \* (Inv572_4aa6_R6_2_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv572_4aa6_R6_2_I1 /\ HandleAppendEntriesResponseAction => Inv572_4aa6_R6_2_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv572_4aa6_R6_2_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv15_1f30_R13_0_I1
THEOREM L_20 == TypeOK /\ Inv15_1f30_R13_0_I1 /\ Next => Inv15_1f30_R13_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv15_1f30_R13_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv15_1f30_R13_0_I1 /\ RequestVoteAction => Inv15_1f30_R13_0_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv15_1f30_R13_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv15_1f30_R13_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv15_1f30_R13_0_I1 /\ UpdateTermAction => Inv15_1f30_R13_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv15_1f30_R13_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv15_1f30_R13_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv15_1f30_R13_0_I1 /\ BecomeLeaderAction => Inv15_1f30_R13_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv15_1f30_R13_0_I1
  \* (Inv15_1f30_R13_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv15_1f30_R13_0_I1 /\ ClientRequestAction => Inv15_1f30_R13_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv15_1f30_R13_0_I1
  \* (Inv15_1f30_R13_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv15_1f30_R13_0_I1 /\ AppendEntriesAction => Inv15_1f30_R13_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv15_1f30_R13_0_I1
  \* (Inv15_1f30_R13_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv15_1f30_R13_0_I1 /\ HandleRequestVoteRequestAction => Inv15_1f30_R13_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv15_1f30_R13_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv15_1f30_R13_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv15_1f30_R13_0_I1 /\ HandleRequestVoteResponseAction => Inv15_1f30_R13_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv15_1f30_R13_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv15_1f30_R13_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv15_1f30_R13_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv15_1f30_R13_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv15_1f30_R13_0_I1
  \* (Inv15_1f30_R13_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv15_1f30_R13_0_I1 /\ HandleAppendEntriesResponseAction => Inv15_1f30_R13_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv15_1f30_R13_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv3_c57a_R6_2_I1
THEOREM L_21 == TypeOK /\ Inv6_441b_R14_1_I1 /\ Inv23_6261_R14_1_I1 /\ Inv31_3acc_R5_1_I1 /\ Inv0_e30e_R11_0_I1 /\ Inv0_2c32_R8_1_I1 /\ Inv16213_37f1_R14_2_I2 /\ Inv9_f533_R11_2_I0 /\ Inv6_2014_R14_0_I0 /\ Inv10_928b_R5_1_I1 /\ Inv3_c57a_R6_2_I1 /\ Next => Inv3_c57a_R6_2_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF H_LogEntryInTermImpliesSafeAtTerm
  \* (Inv3_c57a_R6_2_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv3_c57a_R6_2_I1 /\ RequestVoteAction => Inv3_c57a_R6_2_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv3_c57a_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv3_c57a_R6_2_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv3_c57a_R6_2_I1 /\ UpdateTermAction => Inv3_c57a_R6_2_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv3_c57a_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv3_c57a_R6_2_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv3_c57a_R6_2_I1 /\ BecomeLeaderAction => Inv3_c57a_R6_2_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv3_c57a_R6_2_I1
  \* (Inv3_c57a_R6_2_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv6_441b_R14_1_I1 /\ Inv23_6261_R14_1_I1 /\ Inv31_3acc_R5_1_I1 /\ Inv0_e30e_R11_0_I1 /\ Inv0_2c32_R8_1_I1 /\ Inv3_c57a_R6_2_I1 /\ ClientRequestAction => Inv3_c57a_R6_2_I1' BY DEF TypeOK,Inv6_441b_R14_1_I1,Inv23_6261_R14_1_I1,Inv31_3acc_R5_1_I1,Inv0_e30e_R11_0_I1,Inv0_2c32_R8_1_I1,ClientRequestAction,ClientRequest,Inv3_c57a_R6_2_I1
  \* (Inv3_c57a_R6_2_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv3_c57a_R6_2_I1 /\ AppendEntriesAction => Inv3_c57a_R6_2_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv3_c57a_R6_2_I1
  \* (Inv3_c57a_R6_2_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv3_c57a_R6_2_I1 /\ HandleRequestVoteRequestAction => Inv3_c57a_R6_2_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_c57a_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv3_c57a_R6_2_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv16213_37f1_R14_2_I2 /\ Inv9_f533_R11_2_I0 /\ Inv3_c57a_R6_2_I1 /\ HandleRequestVoteResponseAction => Inv3_c57a_R6_2_I1' BY DEF TypeOK,Inv16213_37f1_R14_2_I2,Inv9_f533_R11_2_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv3_c57a_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv3_c57a_R6_2_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv6_2014_R14_0_I0 /\ Inv10_928b_R5_1_I1 /\ Inv3_c57a_R6_2_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv3_c57a_R6_2_I1' BY DEF TypeOK,Inv6_2014_R14_0_I0,Inv10_928b_R5_1_I1,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv3_c57a_R6_2_I1
  \* (Inv3_c57a_R6_2_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv3_c57a_R6_2_I1 /\ HandleAppendEntriesResponseAction => Inv3_c57a_R6_2_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv3_c57a_R6_2_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv6_2014_R14_0_I0
THEOREM L_22 == TypeOK /\ Inv247_73fd_R25_0_I1 /\ Inv12_0a54_R25_0_I1 /\ Inv6_441b_R14_1_I1 /\ Inv23_bf9f_R16_0_I0 /\ Inv6_2014_R14_0_I0 /\ Next => Inv6_2014_R14_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF H_LogEntryInTermImpliesSafeAtTermAppendEntries
  \* (Inv6_2014_R14_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv6_2014_R14_0_I0 /\ RequestVoteAction => Inv6_2014_R14_0_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv6_2014_R14_0_I0,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i)
                 PROVE  Inv6_2014_R14_0_I0'
      BY DEF RequestVoteAction
    <2>1. H_LogEntryInTermImpliesSafeAtTermAppendEntries'
      <3> SUFFICES ASSUME NEW m \in appendEntriesRequestMsgs',
                          (/\ m.mtype = AppendEntriesRequest
                           /\ m.mentries # <<>>)'
                   PROVE  (\E Q \in Quorum : 
                           \E u \in Server : 
                               /\ currentTerm[u] >= m.mentries[1]
                               /\ (currentTerm[u] = m.mentries[1]) => state[u] = Leader
                               /\ \A n \in Q : 
                                   /\ currentTerm[n] >= m.mentries[1]
                                   /\ currentTerm[n] = m.mentries[1] => (votedFor[n] = u))'
        BY DEF H_LogEntryInTermImpliesSafeAtTermAppendEntries
      <3> QED
        BY DEF TypeOK,RequestVoteAction,RequestVote,Inv6_2014_R14_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
      
    <2>2. (currentTerm = currentTerm)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv6_2014_R14_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>3. (state = state)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv6_2014_R14_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>4. (log = log)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv6_2014_R14_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>5. (votedFor = votedFor)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv6_2014_R14_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>6. (appendEntriesRequestMsgs = appendEntriesRequestMsgs)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv6_2014_R14_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>7. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Inv6_2014_R14_0_I0
  \* (Inv6_2014_R14_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv6_2014_R14_0_I0 /\ UpdateTermAction => Inv6_2014_R14_0_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv6_2014_R14_0_I0,
                        TRUE,
                        NEW m \in requestVoteRequestMsgs \cup requestVoteResponseMsgs \cup appendEntriesRequestMsgs \cup appendEntriesResponseMsgs,
                        UpdateTerm(m.mterm, m.mdest)
                 PROVE  Inv6_2014_R14_0_I0'
      BY DEF UpdateTermAction
    <2>1. H_LogEntryInTermImpliesSafeAtTermAppendEntries'
      BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv6_2014_R14_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>2. (currentTerm = currentTerm)'
      BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv6_2014_R14_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>3. (state = state)'
      BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv6_2014_R14_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>4. (log = log)'
      BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv6_2014_R14_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>5. (votedFor = votedFor)'
      BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv6_2014_R14_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>6. (appendEntriesRequestMsgs = appendEntriesRequestMsgs)'
      BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv6_2014_R14_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>7. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Inv6_2014_R14_0_I0
  \* (Inv6_2014_R14_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv6_2014_R14_0_I0 /\ BecomeLeaderAction => Inv6_2014_R14_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv6_2014_R14_0_I0
  \* (Inv6_2014_R14_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv6_2014_R14_0_I0 /\ ClientRequestAction => Inv6_2014_R14_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv6_2014_R14_0_I0
  \* (Inv6_2014_R14_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv247_73fd_R25_0_I1 /\ Inv12_0a54_R25_0_I1 /\ Inv6_441b_R14_1_I1 /\ Inv23_bf9f_R16_0_I0 /\ Inv6_2014_R14_0_I0 /\ AppendEntriesAction => Inv6_2014_R14_0_I0' BY DEF TypeOK,Inv247_73fd_R25_0_I1,Inv12_0a54_R25_0_I1,Inv6_441b_R14_1_I1,Inv23_bf9f_R16_0_I0,AppendEntriesAction,AppendEntries,Inv6_2014_R14_0_I0
  \* (Inv6_2014_R14_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv6_2014_R14_0_I0 /\ HandleRequestVoteRequestAction => Inv6_2014_R14_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv6_2014_R14_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6_2014_R14_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv6_2014_R14_0_I0 /\ HandleRequestVoteResponseAction => Inv6_2014_R14_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv6_2014_R14_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6_2014_R14_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv6_2014_R14_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv6_2014_R14_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv6_2014_R14_0_I0
  \* (Inv6_2014_R14_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv6_2014_R14_0_I0 /\ HandleAppendEntriesResponseAction => Inv6_2014_R14_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv6_2014_R14_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv247_73fd_R25_0_I1
THEOREM L_23 == TypeOK /\ Inv247_73fd_R25_0_I1 /\ Next => Inv247_73fd_R25_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv247_73fd_R25_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv247_73fd_R25_0_I1 /\ RequestVoteAction => Inv247_73fd_R25_0_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv247_73fd_R25_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv247_73fd_R25_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv247_73fd_R25_0_I1 /\ UpdateTermAction => Inv247_73fd_R25_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv247_73fd_R25_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv247_73fd_R25_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv247_73fd_R25_0_I1 /\ BecomeLeaderAction => Inv247_73fd_R25_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv247_73fd_R25_0_I1
  \* (Inv247_73fd_R25_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv247_73fd_R25_0_I1 /\ ClientRequestAction => Inv247_73fd_R25_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv247_73fd_R25_0_I1
  \* (Inv247_73fd_R25_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv247_73fd_R25_0_I1 /\ AppendEntriesAction => Inv247_73fd_R25_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv247_73fd_R25_0_I1
  \* (Inv247_73fd_R25_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv247_73fd_R25_0_I1 /\ HandleRequestVoteRequestAction => Inv247_73fd_R25_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv247_73fd_R25_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv247_73fd_R25_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv247_73fd_R25_0_I1 /\ HandleRequestVoteResponseAction => Inv247_73fd_R25_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv247_73fd_R25_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv247_73fd_R25_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv247_73fd_R25_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv247_73fd_R25_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv247_73fd_R25_0_I1
  \* (Inv247_73fd_R25_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv247_73fd_R25_0_I1 /\ HandleAppendEntriesResponseAction => Inv247_73fd_R25_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv247_73fd_R25_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv12_0a54_R25_0_I1
THEOREM L_24 == TypeOK /\ Inv12_0a54_R25_0_I1 /\ Next => Inv12_0a54_R25_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv12_0a54_R25_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv12_0a54_R25_0_I1 /\ RequestVoteAction => Inv12_0a54_R25_0_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv12_0a54_R25_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv12_0a54_R25_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv12_0a54_R25_0_I1 /\ UpdateTermAction => Inv12_0a54_R25_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv12_0a54_R25_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv12_0a54_R25_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv12_0a54_R25_0_I1 /\ BecomeLeaderAction => Inv12_0a54_R25_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv12_0a54_R25_0_I1
  \* (Inv12_0a54_R25_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv12_0a54_R25_0_I1 /\ ClientRequestAction => Inv12_0a54_R25_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv12_0a54_R25_0_I1
  \* (Inv12_0a54_R25_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv12_0a54_R25_0_I1 /\ AppendEntriesAction => Inv12_0a54_R25_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv12_0a54_R25_0_I1
  \* (Inv12_0a54_R25_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv12_0a54_R25_0_I1 /\ HandleRequestVoteRequestAction => Inv12_0a54_R25_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv12_0a54_R25_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv12_0a54_R25_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv12_0a54_R25_0_I1 /\ HandleRequestVoteResponseAction => Inv12_0a54_R25_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv12_0a54_R25_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv12_0a54_R25_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv12_0a54_R25_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv12_0a54_R25_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv12_0a54_R25_0_I1
  \* (Inv12_0a54_R25_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv12_0a54_R25_0_I1 /\ HandleAppendEntriesResponseAction => Inv12_0a54_R25_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv12_0a54_R25_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv6_441b_R14_1_I1
THEOREM L_25 == TypeOK /\ Inv247_73fd_R25_0_I1 /\ Inv0_2c32_R8_1_I1 /\ Inv0_e30e_R11_0_I1 /\ Inv6_441b_R14_1_I1 /\ Next => Inv6_441b_R14_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF H_QuorumsSafeAtTerms
  \* (Inv6_441b_R14_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv6_441b_R14_1_I1 /\ RequestVoteAction => Inv6_441b_R14_1_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv6_441b_R14_1_I1,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i)
                 PROVE  Inv6_441b_R14_1_I1'
      BY DEF RequestVoteAction
    <2>1. H_QuorumsSafeAtTerms'
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv6_441b_R14_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>2. (currentTerm = currentTerm)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv6_441b_R14_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>3. (state = state)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv6_441b_R14_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>4. (votedFor = votedFor)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv6_441b_R14_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4 DEF Inv6_441b_R14_1_I1
  \* (Inv6_441b_R14_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv6_441b_R14_1_I1 /\ UpdateTermAction => Inv6_441b_R14_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv6_441b_R14_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6_441b_R14_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv247_73fd_R25_0_I1 /\ Inv0_2c32_R8_1_I1 /\ Inv0_e30e_R11_0_I1 /\ Inv6_441b_R14_1_I1 /\ BecomeLeaderAction => Inv6_441b_R14_1_I1' BY DEF TypeOK,Inv247_73fd_R25_0_I1,Inv0_2c32_R8_1_I1,Inv0_e30e_R11_0_I1,BecomeLeaderAction,BecomeLeader,Inv6_441b_R14_1_I1
  \* (Inv6_441b_R14_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv6_441b_R14_1_I1 /\ ClientRequestAction => Inv6_441b_R14_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv6_441b_R14_1_I1
  \* (Inv6_441b_R14_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv6_441b_R14_1_I1 /\ AppendEntriesAction => Inv6_441b_R14_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv6_441b_R14_1_I1
  \* (Inv6_441b_R14_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv6_441b_R14_1_I1 /\ HandleRequestVoteRequestAction => Inv6_441b_R14_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv6_441b_R14_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6_441b_R14_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv6_441b_R14_1_I1 /\ HandleRequestVoteResponseAction => Inv6_441b_R14_1_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv6_441b_R14_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6_441b_R14_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv6_441b_R14_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv6_441b_R14_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv6_441b_R14_1_I1
  \* (Inv6_441b_R14_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv6_441b_R14_1_I1 /\ HandleAppendEntriesResponseAction => Inv6_441b_R14_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv6_441b_R14_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv23_bf9f_R16_0_I0
THEOREM L_26 == TypeOK /\ Inv76_9fea_R16_1_I1 /\ Inv23_bf9f_R16_0_I0 /\ Next => Inv23_bf9f_R16_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv23_bf9f_R16_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv23_bf9f_R16_0_I0 /\ RequestVoteAction => Inv23_bf9f_R16_0_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv23_bf9f_R16_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv23_bf9f_R16_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv23_bf9f_R16_0_I0 /\ UpdateTermAction => Inv23_bf9f_R16_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv23_bf9f_R16_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv23_bf9f_R16_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv23_bf9f_R16_0_I0 /\ BecomeLeaderAction => Inv23_bf9f_R16_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv23_bf9f_R16_0_I0
  \* (Inv23_bf9f_R16_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv23_bf9f_R16_0_I0 /\ ClientRequestAction => Inv23_bf9f_R16_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv23_bf9f_R16_0_I0
  \* (Inv23_bf9f_R16_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv23_bf9f_R16_0_I0 /\ AppendEntriesAction => Inv23_bf9f_R16_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv23_bf9f_R16_0_I0
  \* (Inv23_bf9f_R16_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv23_bf9f_R16_0_I0 /\ HandleRequestVoteRequestAction => Inv23_bf9f_R16_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv23_bf9f_R16_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv23_bf9f_R16_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv23_bf9f_R16_0_I0 /\ HandleRequestVoteResponseAction => Inv23_bf9f_R16_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv23_bf9f_R16_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv23_bf9f_R16_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv76_9fea_R16_1_I1 /\ Inv23_bf9f_R16_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv23_bf9f_R16_0_I0' BY DEF TypeOK,Inv76_9fea_R16_1_I1,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv23_bf9f_R16_0_I0
  \* (Inv23_bf9f_R16_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv23_bf9f_R16_0_I0 /\ HandleAppendEntriesResponseAction => Inv23_bf9f_R16_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv23_bf9f_R16_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv76_9fea_R16_1_I1
THEOREM L_27 == TypeOK /\ Inv23_bf9f_R16_0_I0 /\ Inv76_9fea_R16_1_I1 /\ Next => Inv76_9fea_R16_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv76_9fea_R16_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv76_9fea_R16_1_I1 /\ RequestVoteAction => Inv76_9fea_R16_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv76_9fea_R16_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv76_9fea_R16_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv76_9fea_R16_1_I1 /\ UpdateTermAction => Inv76_9fea_R16_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv76_9fea_R16_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv76_9fea_R16_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv76_9fea_R16_1_I1 /\ BecomeLeaderAction => Inv76_9fea_R16_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv76_9fea_R16_1_I1
  \* (Inv76_9fea_R16_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv76_9fea_R16_1_I1 /\ ClientRequestAction => Inv76_9fea_R16_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv76_9fea_R16_1_I1
  \* (Inv76_9fea_R16_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv23_bf9f_R16_0_I0 /\ Inv76_9fea_R16_1_I1 /\ AppendEntriesAction => Inv76_9fea_R16_1_I1' BY DEF TypeOK,Inv23_bf9f_R16_0_I0,AppendEntriesAction,AppendEntries,Inv76_9fea_R16_1_I1
  \* (Inv76_9fea_R16_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv76_9fea_R16_1_I1 /\ HandleRequestVoteRequestAction => Inv76_9fea_R16_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv76_9fea_R16_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv76_9fea_R16_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv76_9fea_R16_1_I1 /\ HandleRequestVoteResponseAction => Inv76_9fea_R16_1_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv76_9fea_R16_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv76_9fea_R16_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv76_9fea_R16_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv76_9fea_R16_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv76_9fea_R16_1_I1
  \* (Inv76_9fea_R16_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv76_9fea_R16_1_I1 /\ HandleAppendEntriesResponseAction => Inv76_9fea_R16_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv76_9fea_R16_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv23_6261_R14_1_I1
THEOREM L_28 == TypeOK /\ Inv23_6261_R14_1_I1 /\ Next => Inv23_6261_R14_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv23_6261_R14_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv23_6261_R14_1_I1 /\ RequestVoteAction => Inv23_6261_R14_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv23_6261_R14_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv23_6261_R14_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv23_6261_R14_1_I1 /\ UpdateTermAction => Inv23_6261_R14_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv23_6261_R14_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv23_6261_R14_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv23_6261_R14_1_I1 /\ BecomeLeaderAction => Inv23_6261_R14_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv23_6261_R14_1_I1
  \* (Inv23_6261_R14_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv23_6261_R14_1_I1 /\ ClientRequestAction => Inv23_6261_R14_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv23_6261_R14_1_I1
  \* (Inv23_6261_R14_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv23_6261_R14_1_I1 /\ AppendEntriesAction => Inv23_6261_R14_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv23_6261_R14_1_I1
  \* (Inv23_6261_R14_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv23_6261_R14_1_I1 /\ HandleRequestVoteRequestAction => Inv23_6261_R14_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv23_6261_R14_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv23_6261_R14_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv23_6261_R14_1_I1 /\ HandleRequestVoteResponseAction => Inv23_6261_R14_1_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv23_6261_R14_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv23_6261_R14_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv23_6261_R14_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv23_6261_R14_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv23_6261_R14_1_I1
  \* (Inv23_6261_R14_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv23_6261_R14_1_I1 /\ HandleAppendEntriesResponseAction => Inv23_6261_R14_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv23_6261_R14_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv16213_37f1_R14_2_I2
THEOREM L_29 == TypeOK /\ Inv9_f533_R11_2_I0 /\ Inv11_3715_R21_0_I0 /\ Inv9_f533_R11_2_I0 /\ Inv11_3715_R21_0_I0 /\ Inv16213_37f1_R14_2_I2 /\ Next => Inv16213_37f1_R14_2_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv16213_37f1_R14_2_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv9_f533_R11_2_I0 /\ Inv11_3715_R21_0_I0 /\ Inv16213_37f1_R14_2_I2 /\ RequestVoteAction => Inv16213_37f1_R14_2_I2' BY DEF TypeOK,Inv9_f533_R11_2_I0,Inv11_3715_R21_0_I0,RequestVoteAction,RequestVote,Inv16213_37f1_R14_2_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv16213_37f1_R14_2_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv9_f533_R11_2_I0 /\ Inv11_3715_R21_0_I0 /\ Inv16213_37f1_R14_2_I2 /\ UpdateTermAction => Inv16213_37f1_R14_2_I2' BY DEF TypeOK,Inv9_f533_R11_2_I0,Inv11_3715_R21_0_I0,UpdateTermAction,UpdateTerm,Inv16213_37f1_R14_2_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv16213_37f1_R14_2_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv16213_37f1_R14_2_I2 /\ BecomeLeaderAction => Inv16213_37f1_R14_2_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv16213_37f1_R14_2_I2
  \* (Inv16213_37f1_R14_2_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv16213_37f1_R14_2_I2 /\ ClientRequestAction => Inv16213_37f1_R14_2_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv16213_37f1_R14_2_I2
  \* (Inv16213_37f1_R14_2_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv16213_37f1_R14_2_I2 /\ AppendEntriesAction => Inv16213_37f1_R14_2_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv16213_37f1_R14_2_I2
  \* (Inv16213_37f1_R14_2_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv16213_37f1_R14_2_I2 /\ HandleRequestVoteRequestAction => Inv16213_37f1_R14_2_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv16213_37f1_R14_2_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv16213_37f1_R14_2_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv16213_37f1_R14_2_I2 /\ HandleRequestVoteResponseAction => Inv16213_37f1_R14_2_I2' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv16213_37f1_R14_2_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv16213_37f1_R14_2_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv16213_37f1_R14_2_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv16213_37f1_R14_2_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv16213_37f1_R14_2_I2
  \* (Inv16213_37f1_R14_2_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv16213_37f1_R14_2_I2 /\ HandleAppendEntriesResponseAction => Inv16213_37f1_R14_2_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv16213_37f1_R14_2_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv22023_0125_R7_1_I2
THEOREM L_30 == TypeOK /\ Inv76_9fea_R16_1_I1 /\ Inv23_bf9f_R16_0_I0 /\ Inv22023_0125_R7_1_I2 /\ Next => Inv22023_0125_R7_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv22023_0125_R7_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv76_9fea_R16_1_I1 /\ Inv22023_0125_R7_1_I2 /\ RequestVoteAction => Inv22023_0125_R7_1_I2' BY DEF TypeOK,Inv76_9fea_R16_1_I1,RequestVoteAction,RequestVote,Inv22023_0125_R7_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv22023_0125_R7_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv22023_0125_R7_1_I2 /\ UpdateTermAction => Inv22023_0125_R7_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv22023_0125_R7_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv22023_0125_R7_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv22023_0125_R7_1_I2 /\ BecomeLeaderAction => Inv22023_0125_R7_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv22023_0125_R7_1_I2
  \* (Inv22023_0125_R7_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv22023_0125_R7_1_I2 /\ ClientRequestAction => Inv22023_0125_R7_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv22023_0125_R7_1_I2
  \* (Inv22023_0125_R7_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv23_bf9f_R16_0_I0 /\ Inv22023_0125_R7_1_I2 /\ AppendEntriesAction => Inv22023_0125_R7_1_I2' BY DEF TypeOK,Inv23_bf9f_R16_0_I0,AppendEntriesAction,AppendEntries,Inv22023_0125_R7_1_I2
  \* (Inv22023_0125_R7_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv22023_0125_R7_1_I2 /\ HandleRequestVoteRequestAction => Inv22023_0125_R7_1_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv22023_0125_R7_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv22023_0125_R7_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv22023_0125_R7_1_I2 /\ HandleRequestVoteResponseAction => Inv22023_0125_R7_1_I2' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv22023_0125_R7_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv22023_0125_R7_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv22023_0125_R7_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv22023_0125_R7_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv22023_0125_R7_1_I2
  \* (Inv22023_0125_R7_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv22023_0125_R7_1_I2 /\ HandleAppendEntriesResponseAction => Inv22023_0125_R7_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv22023_0125_R7_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv11181_2cfb_R7_1_I2
THEOREM L_31 == TypeOK /\ Inv6_3122_R17_0_I1 /\ Inv10_928b_R5_1_I1 /\ Inv387_09bb_R9_0_I1 /\ Inv11181_2cfb_R7_1_I2 /\ Next => Inv11181_2cfb_R7_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv11181_2cfb_R7_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv11181_2cfb_R7_1_I2 /\ RequestVoteAction => Inv11181_2cfb_R7_1_I2' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv11181_2cfb_R7_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv11181_2cfb_R7_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv11181_2cfb_R7_1_I2 /\ UpdateTermAction => Inv11181_2cfb_R7_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv11181_2cfb_R7_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv11181_2cfb_R7_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv11181_2cfb_R7_1_I2 /\ BecomeLeaderAction => Inv11181_2cfb_R7_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv11181_2cfb_R7_1_I2
  \* (Inv11181_2cfb_R7_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv11181_2cfb_R7_1_I2 /\ ClientRequestAction => Inv11181_2cfb_R7_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv11181_2cfb_R7_1_I2
  \* (Inv11181_2cfb_R7_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv11181_2cfb_R7_1_I2 /\ AppendEntriesAction => Inv11181_2cfb_R7_1_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv11181_2cfb_R7_1_I2
  \* (Inv11181_2cfb_R7_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv6_3122_R17_0_I1 /\ Inv10_928b_R5_1_I1 /\ Inv387_09bb_R9_0_I1 /\ Inv11181_2cfb_R7_1_I2 /\ HandleRequestVoteRequestAction => Inv11181_2cfb_R7_1_I2' BY DEF TypeOK,Inv6_3122_R17_0_I1,Inv10_928b_R5_1_I1,Inv387_09bb_R9_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv11181_2cfb_R7_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv11181_2cfb_R7_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv11181_2cfb_R7_1_I2 /\ HandleRequestVoteResponseAction => Inv11181_2cfb_R7_1_I2' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv11181_2cfb_R7_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv11181_2cfb_R7_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv11181_2cfb_R7_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv11181_2cfb_R7_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv11181_2cfb_R7_1_I2
  \* (Inv11181_2cfb_R7_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv11181_2cfb_R7_1_I2 /\ HandleAppendEntriesResponseAction => Inv11181_2cfb_R7_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv11181_2cfb_R7_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv28824_2ce2_R7_1_I2
THEOREM L_32 == TypeOK /\ Inv0_2c32_R8_1_I1 /\ Inv9_f533_R11_2_I0 /\ Inv28824_2ce2_R7_1_I2 /\ Next => Inv28824_2ce2_R7_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv28824_2ce2_R7_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv28824_2ce2_R7_1_I2 /\ RequestVoteAction => Inv28824_2ce2_R7_1_I2' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv28824_2ce2_R7_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv28824_2ce2_R7_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv28824_2ce2_R7_1_I2 /\ UpdateTermAction => Inv28824_2ce2_R7_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv28824_2ce2_R7_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv28824_2ce2_R7_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv0_2c32_R8_1_I1 /\ Inv28824_2ce2_R7_1_I2 /\ BecomeLeaderAction => Inv28824_2ce2_R7_1_I2' BY DEF TypeOK,Inv0_2c32_R8_1_I1,BecomeLeaderAction,BecomeLeader,Inv28824_2ce2_R7_1_I2
  \* (Inv28824_2ce2_R7_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv28824_2ce2_R7_1_I2 /\ ClientRequestAction => Inv28824_2ce2_R7_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv28824_2ce2_R7_1_I2
  \* (Inv28824_2ce2_R7_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv28824_2ce2_R7_1_I2 /\ AppendEntriesAction => Inv28824_2ce2_R7_1_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv28824_2ce2_R7_1_I2
  \* (Inv28824_2ce2_R7_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv28824_2ce2_R7_1_I2 /\ HandleRequestVoteRequestAction => Inv28824_2ce2_R7_1_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv28824_2ce2_R7_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv28824_2ce2_R7_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv9_f533_R11_2_I0 /\ Inv28824_2ce2_R7_1_I2 /\ HandleRequestVoteResponseAction => Inv28824_2ce2_R7_1_I2' BY DEF TypeOK,Inv9_f533_R11_2_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv28824_2ce2_R7_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv28824_2ce2_R7_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv28824_2ce2_R7_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv28824_2ce2_R7_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv28824_2ce2_R7_1_I2
  \* (Inv28824_2ce2_R7_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv28824_2ce2_R7_1_I2 /\ HandleAppendEntriesResponseAction => Inv28824_2ce2_R7_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv28824_2ce2_R7_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv5_1e2e_R6_3_I1
THEOREM L_33 == TypeOK /\ Inv3_9e78_R15_0_I0 /\ Inv5_1e2e_R6_3_I1 /\ Next => Inv5_1e2e_R6_3_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv5_1e2e_R6_3_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv5_1e2e_R6_3_I1 /\ RequestVoteAction => Inv5_1e2e_R6_3_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv5_1e2e_R6_3_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5_1e2e_R6_3_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv5_1e2e_R6_3_I1 /\ UpdateTermAction => Inv5_1e2e_R6_3_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv5_1e2e_R6_3_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5_1e2e_R6_3_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv5_1e2e_R6_3_I1 /\ BecomeLeaderAction => Inv5_1e2e_R6_3_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv5_1e2e_R6_3_I1
  \* (Inv5_1e2e_R6_3_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv5_1e2e_R6_3_I1 /\ ClientRequestAction => Inv5_1e2e_R6_3_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv5_1e2e_R6_3_I1
  \* (Inv5_1e2e_R6_3_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv5_1e2e_R6_3_I1 /\ AppendEntriesAction => Inv5_1e2e_R6_3_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv5_1e2e_R6_3_I1
  \* (Inv5_1e2e_R6_3_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv3_9e78_R15_0_I0 /\ Inv5_1e2e_R6_3_I1 /\ HandleRequestVoteRequestAction => Inv5_1e2e_R6_3_I1' BY DEF TypeOK,Inv3_9e78_R15_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_1e2e_R6_3_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5_1e2e_R6_3_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv5_1e2e_R6_3_I1 /\ HandleRequestVoteResponseAction => Inv5_1e2e_R6_3_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv5_1e2e_R6_3_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5_1e2e_R6_3_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv5_1e2e_R6_3_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv5_1e2e_R6_3_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv5_1e2e_R6_3_I1
  \* (Inv5_1e2e_R6_3_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv5_1e2e_R6_3_I1 /\ HandleAppendEntriesResponseAction => Inv5_1e2e_R6_3_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv5_1e2e_R6_3_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv3_9e78_R15_0_I0
THEOREM L_34 == TypeOK /\ Inv3_9e78_R15_0_I0 /\ Next => Inv3_9e78_R15_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv3_9e78_R15_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv3_9e78_R15_0_I0 /\ RequestVoteAction => Inv3_9e78_R15_0_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv3_9e78_R15_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv3_9e78_R15_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv3_9e78_R15_0_I0 /\ UpdateTermAction => Inv3_9e78_R15_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv3_9e78_R15_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv3_9e78_R15_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv3_9e78_R15_0_I0 /\ BecomeLeaderAction => Inv3_9e78_R15_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv3_9e78_R15_0_I0
  \* (Inv3_9e78_R15_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv3_9e78_R15_0_I0 /\ ClientRequestAction => Inv3_9e78_R15_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv3_9e78_R15_0_I0
  \* (Inv3_9e78_R15_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv3_9e78_R15_0_I0 /\ AppendEntriesAction => Inv3_9e78_R15_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv3_9e78_R15_0_I0
  \* (Inv3_9e78_R15_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv3_9e78_R15_0_I0 /\ HandleRequestVoteRequestAction => Inv3_9e78_R15_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_9e78_R15_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv3_9e78_R15_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv3_9e78_R15_0_I0 /\ HandleRequestVoteResponseAction => Inv3_9e78_R15_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv3_9e78_R15_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv3_9e78_R15_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv3_9e78_R15_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv3_9e78_R15_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv3_9e78_R15_0_I0
  \* (Inv3_9e78_R15_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv3_9e78_R15_0_I0 /\ HandleAppendEntriesResponseAction => Inv3_9e78_R15_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv3_9e78_R15_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv23620_5cd3_R6_1_I2
THEOREM L_35 == TypeOK /\ Inv5_1e2e_R6_3_I1 /\ Inv3_8e53_R5_0_I0 /\ Inv5_42ac_R5_1_I1 /\ Inv572_4aa6_R6_2_I1 /\ Inv0_e30e_R11_0_I1 /\ Inv23620_5cd3_R6_1_I2 /\ Next => Inv23620_5cd3_R6_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF GrantedVoteSet
  \* (Inv23620_5cd3_R6_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv5_1e2e_R6_3_I1 /\ Inv23620_5cd3_R6_1_I2 /\ RequestVoteAction => Inv23620_5cd3_R6_1_I2' BY DEF TypeOK,Inv5_1e2e_R6_3_I1,RequestVoteAction,RequestVote,Inv23620_5cd3_R6_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv23620_5cd3_R6_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv23620_5cd3_R6_1_I2 /\ UpdateTermAction => Inv23620_5cd3_R6_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv23620_5cd3_R6_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv23620_5cd3_R6_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv3_8e53_R5_0_I0 /\ Inv5_42ac_R5_1_I1 /\ Inv23620_5cd3_R6_1_I2 /\ BecomeLeaderAction => Inv23620_5cd3_R6_1_I2' BY DEF TypeOK,Inv3_8e53_R5_0_I0,Inv5_42ac_R5_1_I1,BecomeLeaderAction,BecomeLeader,Inv23620_5cd3_R6_1_I2
  \* (Inv23620_5cd3_R6_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv23620_5cd3_R6_1_I2 /\ ClientRequestAction => Inv23620_5cd3_R6_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv23620_5cd3_R6_1_I2
  \* (Inv23620_5cd3_R6_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv23620_5cd3_R6_1_I2 /\ AppendEntriesAction => Inv23620_5cd3_R6_1_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv23620_5cd3_R6_1_I2
  \* (Inv23620_5cd3_R6_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv572_4aa6_R6_2_I1 /\ Inv0_e30e_R11_0_I1 /\ Inv23620_5cd3_R6_1_I2 /\ HandleRequestVoteRequestAction => Inv23620_5cd3_R6_1_I2' BY DEF TypeOK,Inv572_4aa6_R6_2_I1,Inv0_e30e_R11_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv23620_5cd3_R6_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv23620_5cd3_R6_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv23620_5cd3_R6_1_I2 /\ HandleRequestVoteResponseAction => Inv23620_5cd3_R6_1_I2' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv23620_5cd3_R6_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv23620_5cd3_R6_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv23620_5cd3_R6_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv23620_5cd3_R6_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv23620_5cd3_R6_1_I2
  \* (Inv23620_5cd3_R6_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv23620_5cd3_R6_1_I2 /\ HandleAppendEntriesResponseAction => Inv23620_5cd3_R6_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv23620_5cd3_R6_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv5_404d_R0_2_I1
THEOREM L_36 == TypeOK /\ Inv11810_6aa7_R2_1_I2 /\ Inv5_404d_R0_2_I1 /\ Next => Inv5_404d_R0_2_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv5_404d_R0_2_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv5_404d_R0_2_I1 /\ RequestVoteAction => Inv5_404d_R0_2_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv5_404d_R0_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5_404d_R0_2_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv5_404d_R0_2_I1 /\ UpdateTermAction => Inv5_404d_R0_2_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv5_404d_R0_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5_404d_R0_2_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv11810_6aa7_R2_1_I2 /\ Inv5_404d_R0_2_I1 /\ BecomeLeaderAction => Inv5_404d_R0_2_I1' BY DEF TypeOK,Inv11810_6aa7_R2_1_I2,BecomeLeaderAction,BecomeLeader,Inv5_404d_R0_2_I1
  \* (Inv5_404d_R0_2_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv5_404d_R0_2_I1 /\ ClientRequestAction => Inv5_404d_R0_2_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv5_404d_R0_2_I1
  \* (Inv5_404d_R0_2_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv5_404d_R0_2_I1 /\ AppendEntriesAction => Inv5_404d_R0_2_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv5_404d_R0_2_I1
  \* (Inv5_404d_R0_2_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv5_404d_R0_2_I1 /\ HandleRequestVoteRequestAction => Inv5_404d_R0_2_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_404d_R0_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5_404d_R0_2_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv5_404d_R0_2_I1 /\ HandleRequestVoteResponseAction => Inv5_404d_R0_2_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv5_404d_R0_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5_404d_R0_2_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv5_404d_R0_2_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv5_404d_R0_2_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv5_404d_R0_2_I1
  \* (Inv5_404d_R0_2_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv5_404d_R0_2_I1 /\ HandleAppendEntriesResponseAction => Inv5_404d_R0_2_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv5_404d_R0_2_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0,A1,A2,A3,A4,A5,A6,A7
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal
    <1>2. Init => Inv32252_9e34_R0_0_I2 BY DEF Init, Inv32252_9e34_R0_0_I2, IndGlobal
    <1>3. Init => Inv44992_e200_R1_1_I2 BY DEF Init, Inv44992_e200_R1_1_I2, IndGlobal
    <1>4. Init => Inv33263_295b_R0_1_I2 BY DEF Init, Inv33263_295b_R0_1_I2, IndGlobal
    <1>5. Init => Inv11810_6aa7_R2_1_I2 BY DEF Init, Inv11810_6aa7_R2_1_I2, IndGlobal
    <1>6. Init => Inv3_8e53_R5_0_I0 BY DEF Init, Inv3_8e53_R5_0_I0, IndGlobal
    <1>7. Init => Inv5_42ac_R5_1_I1 BY DEF Init, Inv5_42ac_R5_1_I1, IndGlobal
    <1>8. Init => Inv0_e30e_R11_0_I1 BY DEF Init, Inv0_e30e_R11_0_I1, IndGlobal
    <1>9. Init => Inv11_3715_R21_0_I0 BY DEF Init, Inv11_3715_R21_0_I0, IndGlobal
    <1>10. Init => Inv9_f533_R11_2_I0 BY DEF Init, Inv9_f533_R11_2_I0, IndGlobal
    <1>11. Init => Inv0_2c32_R8_1_I1 BY DEF Init, Inv0_2c32_R8_1_I1, IndGlobal
    <1>12. Init => Inv5_82b3_R11_1_I0 BY DEF Init, Inv5_82b3_R11_1_I0, IndGlobal
    <1>13. Init => Inv10_928b_R5_1_I1 BY DEF Init, Inv10_928b_R5_1_I1, IndGlobal
    <1>14. Init => Inv387_09bb_R9_0_I1 BY DEF Init, Inv387_09bb_R9_0_I1, IndGlobal
    <1>15. Init => Inv6_3122_R17_0_I1 BY DEF Init, Inv6_3122_R17_0_I1, IndGlobal
    <1>16. Init => Inv31_3acc_R5_1_I1 BY DEF Init, Inv31_3acc_R5_1_I1, IndGlobal
    <1>17. Init => Inv22719_8a29_R2_2_I2 BY DEF Init, Inv22719_8a29_R2_2_I2, IndGlobal
    <1>18. Init => Inv34192_7f3f_R4_1_I2 BY DEF Init, Inv34192_7f3f_R4_1_I2, IndGlobal
    <1>19. Init => Inv572_4aa6_R6_2_I1 BY DEF Init, Inv572_4aa6_R6_2_I1, IndGlobal
    <1>20. Init => Inv15_1f30_R13_0_I1 BY DEF Init, Inv15_1f30_R13_0_I1, IndGlobal
    <1>21. Init => Inv3_c57a_R6_2_I1 BY DEF Init, Inv3_c57a_R6_2_I1, IndGlobal
    <1>22. Init => Inv6_2014_R14_0_I0 BY DEF Init, Inv6_2014_R14_0_I0, IndGlobal
    <1>23. Init => Inv247_73fd_R25_0_I1 BY DEF Init, Inv247_73fd_R25_0_I1, IndGlobal
    <1>24. Init => Inv12_0a54_R25_0_I1 BY DEF Init, Inv12_0a54_R25_0_I1, IndGlobal
    <1>25. Init => Inv6_441b_R14_1_I1 BY DEF Init, Inv6_441b_R14_1_I1, IndGlobal
    <1>26. Init => Inv23_bf9f_R16_0_I0 BY DEF Init, Inv23_bf9f_R16_0_I0, IndGlobal
    <1>27. Init => Inv76_9fea_R16_1_I1 BY DEF Init, Inv76_9fea_R16_1_I1, IndGlobal
    <1>28. Init => Inv23_6261_R14_1_I1 BY DEF Init, Inv23_6261_R14_1_I1, IndGlobal
    <1>29. Init => Inv16213_37f1_R14_2_I2 BY DEF Init, Inv16213_37f1_R14_2_I2, IndGlobal
    <1>30. Init => Inv22023_0125_R7_1_I2 BY DEF Init, Inv22023_0125_R7_1_I2, IndGlobal
    <1>31. Init => Inv11181_2cfb_R7_1_I2 BY DEF Init, Inv11181_2cfb_R7_1_I2, IndGlobal
    <1>32. Init => Inv28824_2ce2_R7_1_I2 BY DEF Init, Inv28824_2ce2_R7_1_I2, IndGlobal
    <1>33. Init => Inv5_1e2e_R6_3_I1 BY DEF Init, Inv5_1e2e_R6_3_I1, IndGlobal
    <1>34. Init => Inv3_9e78_R15_0_I0 BY DEF Init, Inv3_9e78_R15_0_I0, IndGlobal
    <1>35. Init => Inv23620_5cd3_R6_1_I2 BY DEF Init, Inv23620_5cd3_R6_1_I2, IndGlobal
    <1>36. Init => Inv5_404d_R0_2_I1 BY DEF Init, Inv5_404d_R0_2_I1, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14,<1>15,<1>16,<1>17,<1>18,<1>19,<1>20,<1>21,<1>22,<1>23,<1>24,<1>25,<1>26,<1>27,<1>28,<1>29,<1>30,<1>31,<1>32,<1>33,<1>34,<1>35,<1>36 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13,L_14,L_15,L_16,L_17,L_18,L_19,L_20,L_21,L_22,L_23,L_24,L_25,L_26,L_27,L_28,L_29,L_30,L_31,L_32,L_33,L_34,L_35,L_36 DEF Next, IndGlobal

====
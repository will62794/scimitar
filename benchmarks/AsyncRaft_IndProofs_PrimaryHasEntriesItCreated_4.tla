--------------------------------- MODULE AsyncRaft_IndProofs_PrimaryHasEntriesItCreated_4 ---------------------------------
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

LEMMA ExistsMax == \A S \in SUBSET Nat : S # {} => \E m \in S : m = Max(S)

\* Proof Graph Stats
\* ==================
\* seed: 4
\* num proof graph nodes: 31
\* num proof obligations: 279
Safety == H_PrimaryHasEntriesItCreated
Inv0_33b0_R0_0_I0 == \A VARI \in Server : \A VARMAEREQ \in appendEntriesRequestMsgs : \A VARLOGINDI \in LogIndices : ((VARLOGINDI \in DOMAIN log[VARI] /\ log[VARI][VARLOGINDI] = currentTerm[VARI]) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI] /\ state[VARI] = Leader)) \/ (~(VARLOGINDI = VARMAEREQ.mprevLogIndex + 1)))
Inv24_ed8d_R0_1_I0 == \A VARI \in Server : \A VARJ \in Server : (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(votesGranted[VARI] \in Quorum)) \/ (~(\E INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] = currentTerm[VARI])))
Inv15_7bad_R0_2_I0 == \A VARI \in Server : \A VARJ \in Server : (~((state[VARI] = Leader /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) \/ (~((state[VARJ] = Leader))))
Inv12_e9c6_R1_1_I0 == \A VARI \in Server : \A VARJ \in Server : \A VARMAEREQ \in appendEntriesRequestMsgs : (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI])) \/ (~(votesGranted[VARI] \in Quorum)))
Inv11_d848_R2_1_I0 == \A VARI \in Server : \A VARJ \in Server : (~((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) \/ (~((state[VARJ] = Leader))) \/ (~(votesGranted[VARI] \in Quorum)))
Inv33_5a2e_R2_2_I0 == \A VARI \in Server : \A VARJ \in Server : (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(\E INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] = currentTerm[VARI])) \/ (~(GrantedVoteSet(VARI) \in Quorum /\ votesGranted = votesGranted /\ requestVoteResponseMsgs = requestVoteResponseMsgs)))
Inv15967_602c_R4_1_I2 == \A VARI \in Server : \A VARJ \in Server : \A VARMAEREQ \in appendEntriesRequestMsgs : ~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(GrantedVoteSet(VARI) \in Quorum /\ votesGranted = votesGranted /\ requestVoteResponseMsgs = requestVoteResponseMsgs)) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI]))
Inv8_8e53_R5_0_I0 == (\A s,t \in Server : ( /\ s # t /\ state[s] \in {Leader,Candidate} /\ state[t] \in {Leader,Candidate} /\ currentTerm[s] = currentTerm[t]) => votesGranted[s] \cap votesGranted[t] = {})
Inv127_0bd2_R5_1_I2 == \A VARI \in Server : \A VARJ \in Server : (VARJ \in votesGranted[VARJ]) \/ (~(VARI \in GrantedVoteSet(VARJ) /\ votesGranted = votesGranted /\ requestVoteResponseMsgs = requestVoteResponseMsgs))
Inv9072_27f5_R5_1_I2 == \A VARI \in Server : \A VARJ \in Server : ((state[VARJ] = Follower)) \/ ((votesGranted[VARI] \in Quorum)) \/ (~((state[VARI] = Leader)))
Inv9_42ac_R5_1_I2 == (\A s,t \in Server : \A m \in requestVoteResponseMsgs :( /\ state[s] \in {Candidate,Leader} /\ t \in votesGranted[s]) => ~(/\ m.mterm = currentTerm[s] /\ m.msource = t /\ m.mdest # s /\ m.mvoteGranted))
Inv82_3acc_R6_1_I1 == \A VARI \in Server : (votesGranted[VARI] \in Quorum) \/ (~((state[VARI] = Leader)))
Inv789_4aa6_R6_2_I1 == \A VARI \in Server : ((state[VARI] = Follower)) \/ ((votedFor[VARI] # Nil /\ VARI \in votesGranted[votedFor[VARI]]))
Inv1281_1f30_R6_2_I1 == \A VARJ \in Server : ((state[VARJ] = Follower)) \/ ((votedFor[VARJ] = VARJ))
Inv4_c57a_R6_2_I1 == (H_LogEntryInTermImpliesSafeAtTerm /\ currentTerm = currentTerm /\ state = state /\ log = log /\ votedFor = votedFor)
Inv2513_1e2e_R6_3_I1 == \A VARREQVRES \in requestVoteResponseMsgs : (currentTerm[VARREQVRES.mdest] >= VARREQVRES.mterm) \/ (~(VARREQVRES.mvoteGranted))
Inv7_8db7_R7_1_I1 == \A VARI \in Server : \A VARJ \in Server : \A VARMAEREQ \in appendEntriesRequestMsgs : ((currentTerm[VARJ] > currentTerm[VARI])) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] > VARMAEREQ.mterm))
Inv173_650b_R7_1_I1 == \A VARREQVRES \in requestVoteResponseMsgs : (H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ currentTerm = currentTerm /\ state = state /\ log = log /\ votedFor = votedFor /\ appendEntriesRequestMsgs = appendEntriesRequestMsgs) \/ (~(currentTerm[VARREQVRES.mdest] >= VARREQVRES.mterm))
Inv0_2c32_R8_1_I1 == \A VARI \in Server : \A VARJ \in Server : ((currentTerm[VARI] <= currentTerm[VARJ])) \/ (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])))
Inv61_fe26_R9_0_I1 == \A VARI \in Server : \A VARREQVM \in requestVoteRequestMsgs : ~(VARREQVM.msource = VARI) \/ (~(votesGranted[VARI] = {}))
Inv166_e30e_R11_0_I1 == \A VARI \in Server : ((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI )) \/ (((state[VARI] = Follower)))
Inv10_82b3_R11_1_I0 == (\A mi,mj \in requestVoteResponseMsgs : (/\ mi.mterm = mj.mterm /\ mi.msource = mj.msource /\ mi.mvoteGranted /\ mj.mvoteGranted) => mi.mdest = mj.mdest)
Inv14_f533_R11_2_I0 == \A VARREQVRES \in requestVoteResponseMsgs : (currentTerm[VARREQVRES.msource] >= VARREQVRES.mterm)
Inv8_2014_R15_0_I0 == (H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ currentTerm = currentTerm /\ state = state /\ log = log /\ votedFor = votedFor /\ appendEntriesRequestMsgs = appendEntriesRequestMsgs)
Inv40_6261_R15_1_I1 == \A VARI \in Server : ((state[VARI] = Follower)) \/ ((VARI \in votesGranted[VARI]))
Inv363_d176_R15_2_I1 == \A VARI \in Server : (\A m \in requestVoteResponseMsgs : m.mtype = RequestVoteResponse =>  /\ (m.mvoteGranted /\ (currentTerm[m.msource] = m.mterm)) => votedFor[m.msource] = m.mdest) \/ (~(votedFor[VARI] # Nil))
Inv12_9e78_R16_0_I0 == \A VARREQVM \in requestVoteRequestMsgs : (currentTerm[VARREQVM.msource] >= VARREQVM.mterm)
Inv11_afc0_R17_0_I0 == \A VARI \in Server : (\A INDK \in DOMAIN log[VARI] : log[VARI][INDK] <= currentTerm[VARI])
Inv13_3715_R21_0_I0 == (\A m \in requestVoteResponseMsgs : m.mtype = RequestVoteResponse =>  /\ (m.mvoteGranted /\ (currentTerm[m.msource] = m.mterm)) => votedFor[m.msource] = m.mdest)
Inv21_c904_R28_0_I0 == \A VARMAEREQ \in appendEntriesRequestMsgs : ~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] > VARMAEREQ.mterm)

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv0_33b0_R0_0_I0
  /\ Inv12_e9c6_R1_1_I0
  /\ Inv24_ed8d_R0_1_I0
  /\ Inv11_d848_R2_1_I0
  /\ Inv8_8e53_R5_0_I0
  /\ Inv9_42ac_R5_1_I2
  /\ Inv166_e30e_R11_0_I1
  /\ Inv13_3715_R21_0_I0
  /\ Inv14_f533_R11_2_I0
  /\ Inv0_2c32_R8_1_I1
  /\ Inv10_82b3_R11_1_I0
  /\ Inv127_0bd2_R5_1_I2
  /\ Inv61_fe26_R9_0_I1
  /\ Inv2513_1e2e_R6_3_I1
  /\ Inv12_9e78_R16_0_I0
  /\ Inv9072_27f5_R5_1_I2
  /\ Inv33_5a2e_R2_2_I0
  /\ Inv15967_602c_R4_1_I2
  /\ Inv789_4aa6_R6_2_I1
  /\ Inv1281_1f30_R6_2_I1
  /\ Inv4_c57a_R6_2_I1
  /\ Inv8_2014_R15_0_I0
  /\ Inv40_6261_R15_1_I1
  /\ Inv82_3acc_R6_1_I1
  /\ Inv363_d176_R15_2_I1
  /\ Inv7_8db7_R7_1_I1
  /\ Inv11_afc0_R17_0_I0
  /\ Inv21_c904_R28_0_I0
  /\ Inv173_650b_R7_1_I1
  /\ Inv15_7bad_R0_2_I0


\* mean in-degree: 2.2903225806451615
\* median in-degree: 1
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

USE AddingToQuorumRemainsQuorum,StaticQuorumsOverlap, FS_Union, FS_Singleton, FS_EmptySet,FS_Subset,ExistsMax DEF LastTerm

\* Helper finitized assumption on Server as check for some harder TLAPS proof obligations.
ASSUME TWO_SERVERS_Assumption == Server = {1,2}
ASSUME THREE_SERVERS_Assumption == Server = {1,2,3}
ASSUME FIVE_SERVERS_Assumption == Server = {1,2,3,4,5}

\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (TypeOK,RequestVoteAction)
  <1>1. TypeOK /\ TypeOK /\ RequestVoteAction => TypeOK' BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (TypeOK,UpdateTermAction)
  <1>2. TypeOK /\ TypeOK /\ UpdateTermAction => TypeOK' BY DEF TypeOK,UpdateTermAction,UpdateTerm,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (TypeOK,BecomeLeaderAction)
  <1>3. TypeOK /\ TypeOK /\ BecomeLeaderAction => TypeOK' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,TypeOK
  \* (TypeOK,ClientRequestAction)
  <1>4. TypeOK /\ TypeOK /\ ClientRequestAction => TypeOK' BY DEF TypeOK,ClientRequestAction,ClientRequest,TypeOK
  \* (TypeOK,AppendEntriesAction)
  <1>5. TypeOK /\ TypeOK /\ AppendEntriesAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK,
                        TypeOK,
                        TRUE,
                        NEW i \in Server, NEW j \in Server,
                        AppendEntries(i, j)
                 PROVE  TypeOK'
      BY DEF AppendEntriesAction
    <2>1. (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>2. (requestVoteResponseMsgs \in SUBSET RequestVoteResponseType)'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>3. (appendEntriesRequestMsgs \in SUBSET AppendEntriesRequestType)'
      BY SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq DEF Min,TypeOK,AppendEntriesAction,AppendEntries,TypeOK,AppendEntriesRequestType
    <2>4. (appendEntriesResponseMsgs \in SUBSET AppendEntriesResponseType)'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>5. (currentTerm \in [Server -> Nat])'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>6. (state       \in [Server -> {Leader, Follower, Candidate}])'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>7. (votedFor    \in [Server -> ({Nil} \cup Server)])'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>8. (votesGranted \in [Server -> (SUBSET Server)])'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>9. (nextIndex  \in [Server -> [Server -> Nat]])'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>10. (matchIndex \in [Server -> [Server -> Nat]])'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>11. (log             \in [Server -> Seq(Nat)])'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>12. (commitIndex     \in [Server -> Nat])'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>13. (\A m \in requestVoteRequestMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>14. (\A m \in requestVoteResponseMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>15. (\A m \in appendEntriesRequestMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>16. (\A m \in appendEntriesResponseMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>17. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
  \* (TypeOK,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ TypeOK /\ HandleRequestVoteRequestAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK,
                        TypeOK,
                        NEW m \in requestVoteRequestMsgs,
                        HandleRequestVoteRequest(m)
                 PROVE  TypeOK'
      BY DEF HandleRequestVoteRequestAction
    <2>1. (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>2. (requestVoteResponseMsgs \in SUBSET RequestVoteResponseType)'
      BY SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
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
    <2>13. (\A m_1 \in requestVoteRequestMsgs : m_1.msource # m_1.mdest)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>14. (\A m_1 \in requestVoteResponseMsgs : m_1.msource # m_1.mdest)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>15. (\A m_1 \in appendEntriesRequestMsgs : m_1.msource # m_1.mdest)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>16. (\A m_1 \in appendEntriesResponseMsgs : m_1.msource # m_1.mdest)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>17. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
  \* (TypeOK,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ TypeOK /\ HandleRequestVoteResponseAction => TypeOK' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (TypeOK,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ TypeOK /\ AcceptAppendEntriesRequestAppendAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK,
                        TypeOK,
                        NEW m \in appendEntriesRequestMsgs,
                        AcceptAppendEntriesRequestAppend(m)
                 PROVE  TypeOK'
      BY DEF AcceptAppendEntriesRequestAppendAction
    <2>1. (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>2. (requestVoteResponseMsgs \in SUBSET RequestVoteResponseType)'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>3. (appendEntriesRequestMsgs \in SUBSET AppendEntriesRequestType)'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>4. (appendEntriesResponseMsgs \in SUBSET AppendEntriesResponseType)'
      BY SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
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
      BY SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq 
      DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK,AppendEntriesResponseType,AppendEntriesRequestType
    <2>12. (commitIndex     \in [Server -> Nat])'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>13. (\A m_1 \in requestVoteRequestMsgs : m_1.msource # m_1.mdest)'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>14. (\A m_1 \in requestVoteResponseMsgs : m_1.msource # m_1.mdest)'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>15. (\A m_1 \in appendEntriesRequestMsgs : m_1.msource # m_1.mdest)'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>16. (\A m_1 \in appendEntriesResponseMsgs : m_1.msource # m_1.mdest)'
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
      BY SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq, ExistsMax
      DEF Max,TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK,AppendEntriesResponseType,AppendEntriesRequestType
    <2>10. (matchIndex \in [Server -> [Server -> Nat]])'
      BY SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq 
      DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK,AppendEntriesResponseType,AppendEntriesRequestType
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
THEOREM L_1 == TypeOK /\ Inv24_ed8d_R0_1_I0 /\ Inv15_7bad_R0_2_I0 /\ Inv0_33b0_R0_0_I0 /\ Safety /\ Next => Safety'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF Safety
  \* (Safety,RequestVoteAction)
  <1>1. TypeOK /\ Safety /\ RequestVoteAction => Safety' BY DEF TypeOK,RequestVoteAction,RequestVote,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,UpdateTermAction)
  <1>2. TypeOK /\ Safety /\ UpdateTermAction => Safety' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv24_ed8d_R0_1_I0 /\ Safety /\ BecomeLeaderAction => Safety' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv24_ed8d_R0_1_I0,
                        Safety,
                        TRUE,
                        NEW i \in Server,
                        BecomeLeader(i)
                 PROVE  Safety'
      BY DEF BecomeLeaderAction
    <2> QED
      BY SMTT(300),FIVE_SERVERS_Assumption DEF TypeOK,Inv24_ed8d_R0_1_I0,BecomeLeaderAction,BecomeLeader,Safety,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,ClientRequestAction)
  <1>4. TypeOK /\ Inv15_7bad_R0_2_I0 /\ Safety /\ ClientRequestAction => Safety' BY DEF TypeOK,Inv15_7bad_R0_2_I0,ClientRequestAction,ClientRequest,Safety,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,AppendEntriesAction)
  <1>5. TypeOK /\ Safety /\ AppendEntriesAction => Safety' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Safety,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Safety /\ HandleRequestVoteRequestAction => Safety' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Safety,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Safety /\ HandleRequestVoteResponseAction => Safety' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Safety,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv0_33b0_R0_0_I0 /\ Safety /\ AcceptAppendEntriesRequestAppendAction => Safety' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv0_33b0_R0_0_I0,
                        Safety,
                        NEW m \in appendEntriesRequestMsgs,
                        AcceptAppendEntriesRequestAppend(m)
                 PROVE  H_PrimaryHasEntriesItCreated'
      BY DEF AcceptAppendEntriesRequestAppendAction
    <2> QED
      <3> SUFFICES ASSUME NEW i \in Server', NEW j \in Server',
                          (state[i] = Leader)'
                   PROVE  (~(\E k \in DOMAIN log[j] :
                               /\ log[j][k] = currentTerm[i]
                               /\ ~\E ind \in DOMAIN log[i] : (ind = k /\ log[i][k] = log[j][k]) 
                               ))'
        BY DEF H_PrimaryHasEntriesItCreated
      <3>1. ((\A k \in DOMAIN log[j] :
                               ~(/\ log[j][k] = currentTerm[i]
                               /\ ~\E ind \in DOMAIN log[i] : (ind = k /\ log[i][k] = log[j][k])) 
                      
                               ))'
        <4> SUFFICES ASSUME NEW k \in (DOMAIN log[j])'
                     PROVE  (~(/\ log[j][k] = currentTerm[i]
                             /\ ~\E ind \in DOMAIN log[i] : (ind = k /\ log[i][k] = log[j][k])))'
          OBVIOUS
        <4> log'[m.mdest] = Append(log[m.mdest], (m.mentries)[1])
\*        <4> log'[Len(log'[m.mdest])] = Append(log'[m.mdest], (m.mentries)[1])
           BY SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq,AppendProperties,AppendIsConcat,SMTT(3000),TWO_SERVERS_Assumption 
                 DEF LogOk,CanAppend,TypeOK,Inv0_33b0_R0_0_I0,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,LogIndices,Safety,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated,AppendEntriesRequestType
         <4> Len(log'[m.mdest]) = Len(log[m.mdest]) + 1
             BY SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq,AppendProperties,AppendIsConcat,SMTT(3000),TWO_SERVERS_Assumption 
         <4> Append(log[m.mdest], m.mentries[1])[Len(log[m.mdest])+1] = m.mentries[1]
          BY SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq,AppendProperties,AppendIsConcat,TWO_SERVERS_Assumption 
           DEF LogOk,CanAppend,TypeOK,Inv0_33b0_R0_0_I0,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,LogIndices,Safety,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated,AppendEntriesRequestType
         <4> log'[m.mdest][Len(log[m.mdest])+1] = (m.mentries)[1]
           BY SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq,AppendProperties,AppendIsConcat,TWO_SERVERS_Assumption 
           DEF LogOk,CanAppend,TypeOK,Inv0_33b0_R0_0_I0,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,LogIndices,Safety,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated,AppendEntriesRequestType
        <4> QED
                 BY SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq,AppendProperties,SMTT(3000),TWO_SERVERS_Assumption 
                 DEF LogOk,CanAppend,TypeOK,Inv0_33b0_R0_0_I0,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,LogIndices,Safety,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated,AppendEntriesRequestType
                               
               
      
      <3> QED
        BY SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq,AppendProperties,SMTT(3000),TWO_SERVERS_Assumption 
        DEF LogOk,CanAppend,TypeOK,Inv0_33b0_R0_0_I0,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,LogIndices,Safety,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated,AppendEntriesRequestType
      
  \* (Safety,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Safety /\ HandleAppendEntriesResponseAction => Safety' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Safety,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv0_33b0_R0_0_I0
THEOREM L_2 == TypeOK /\ Inv12_e9c6_R1_1_I0 /\ Safety /\ Inv0_33b0_R0_0_I0 /\ Next => Inv0_33b0_R0_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv0_33b0_R0_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv0_33b0_R0_0_I0 /\ RequestVoteAction => Inv0_33b0_R0_0_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv0_33b0_R0_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv0_33b0_R0_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv0_33b0_R0_0_I0 /\ UpdateTermAction => Inv0_33b0_R0_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv0_33b0_R0_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv0_33b0_R0_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv12_e9c6_R1_1_I0 /\ Inv0_33b0_R0_0_I0 /\ BecomeLeaderAction => Inv0_33b0_R0_0_I0' BY DEF TypeOK,Inv12_e9c6_R1_1_I0,BecomeLeaderAction,BecomeLeader,Inv0_33b0_R0_0_I0
  \* (Inv0_33b0_R0_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv0_33b0_R0_0_I0 /\ ClientRequestAction => Inv0_33b0_R0_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv0_33b0_R0_0_I0
  \* (Inv0_33b0_R0_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Safety /\ Inv0_33b0_R0_0_I0 /\ AppendEntriesAction => Inv0_33b0_R0_0_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Safety,
                        Inv0_33b0_R0_0_I0,
                        TRUE,
                        NEW i \in Server, NEW j \in Server,
                        AppendEntries(i, j),
                        NEW VARI \in Server',
                        NEW VARMAEREQ \in appendEntriesRequestMsgs',
                        NEW VARLOGINDI \in LogIndices'
                 PROVE  ((VARLOGINDI \in DOMAIN log[VARI] /\ log[VARI][VARLOGINDI] = currentTerm[VARI]) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI] /\ state[VARI] = Leader)) \/ (~(VARLOGINDI = VARMAEREQ.mprevLogIndex + 1)))'
      BY DEF AppendEntriesAction, Inv0_33b0_R0_0_I0
    <2> QED
      BY THREE_SERVERS_Assumption,SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq 
      DEF Min,TypeOK,Safety,AppendEntriesAction,AppendEntries,Inv0_33b0_R0_0_I0, AppendEntriesRequestType, AppendEntriesResponseType
  \* (Inv0_33b0_R0_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv0_33b0_R0_0_I0 /\ HandleRequestVoteRequestAction => Inv0_33b0_R0_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv0_33b0_R0_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_33b0_R0_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv0_33b0_R0_0_I0 /\ HandleRequestVoteResponseAction => Inv0_33b0_R0_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv0_33b0_R0_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_33b0_R0_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv0_33b0_R0_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv0_33b0_R0_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv0_33b0_R0_0_I0
  \* (Inv0_33b0_R0_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv0_33b0_R0_0_I0 /\ HandleAppendEntriesResponseAction => Inv0_33b0_R0_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv0_33b0_R0_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv12_e9c6_R1_1_I0
THEOREM L_3 == TypeOK /\ Inv24_ed8d_R0_1_I0 /\ Inv15967_602c_R4_1_I2 /\ Inv12_e9c6_R1_1_I0 /\ Next => Inv12_e9c6_R1_1_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv12_e9c6_R1_1_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv12_e9c6_R1_1_I0 /\ RequestVoteAction => Inv12_e9c6_R1_1_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv12_e9c6_R1_1_I0,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server',
                        NEW VARMAEREQ \in appendEntriesRequestMsgs'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI])) \/ (~(votesGranted[VARI] \in Quorum)))'
      BY DEF Inv12_e9c6_R1_1_I0, RequestVoteAction
    <2> QED
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv12_e9c6_R1_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv12_e9c6_R1_1_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv12_e9c6_R1_1_I0 /\ UpdateTermAction => Inv12_e9c6_R1_1_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv12_e9c6_R1_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv12_e9c6_R1_1_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv12_e9c6_R1_1_I0 /\ BecomeLeaderAction => Inv12_e9c6_R1_1_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv12_e9c6_R1_1_I0
  \* (Inv12_e9c6_R1_1_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv12_e9c6_R1_1_I0 /\ ClientRequestAction => Inv12_e9c6_R1_1_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv12_e9c6_R1_1_I0
  \* (Inv12_e9c6_R1_1_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv24_ed8d_R0_1_I0 /\ Inv12_e9c6_R1_1_I0 /\ AppendEntriesAction => Inv12_e9c6_R1_1_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv24_ed8d_R0_1_I0,
                        Inv12_e9c6_R1_1_I0,
                        TRUE,
                        NEW i \in Server, NEW j \in Server,
                        AppendEntries(i, j),
                        NEW VARI \in Server',
                        NEW VARJ \in Server',
                        NEW VARMAEREQ \in appendEntriesRequestMsgs'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI])) \/ (~(votesGranted[VARI] \in Quorum)))'
      BY DEF AppendEntriesAction, Inv12_e9c6_R1_1_I0
    <2> QED
      BY SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq,TWO_SERVERS_Assumption,SMTT(300) 
      DEF TypeOK,Inv24_ed8d_R0_1_I0,AppendEntriesAction,AppendEntries,Inv12_e9c6_R1_1_I0,AppendEntriesRequestType,AppendEntriesResponseType,RequestVoteResponseType
  \* (Inv12_e9c6_R1_1_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv12_e9c6_R1_1_I0 /\ HandleRequestVoteRequestAction => Inv12_e9c6_R1_1_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv12_e9c6_R1_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv12_e9c6_R1_1_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv15967_602c_R4_1_I2 /\ Inv12_e9c6_R1_1_I0 /\ HandleRequestVoteResponseAction => Inv12_e9c6_R1_1_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv15967_602c_R4_1_I2,
                        Inv12_e9c6_R1_1_I0,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server',
                        NEW VARJ \in Server',
                        NEW VARMAEREQ \in appendEntriesRequestMsgs'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI])) \/ (~(votesGranted[VARI] \in Quorum)))'
      BY DEF HandleRequestVoteResponseAction, Inv12_e9c6_R1_1_I0
    <2> QED
      BY TWO_SERVERS_Assumption,SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq,SMTT(300)
      DEF TypeOK,Inv15967_602c_R4_1_I2,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv12_e9c6_R1_1_I0,LastTerm,AppendEntriesRequestType,AppendEntriesResponseType,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv12_e9c6_R1_1_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv12_e9c6_R1_1_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv12_e9c6_R1_1_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv12_e9c6_R1_1_I0
  \* (Inv12_e9c6_R1_1_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv12_e9c6_R1_1_I0 /\ HandleAppendEntriesResponseAction => Inv12_e9c6_R1_1_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv12_e9c6_R1_1_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next

\*** Inv24_ed8d_R0_1_I0
THEOREM L_4 == TypeOK /\ Inv11_d848_R2_1_I0 /\ Inv33_5a2e_R2_2_I0 /\ Inv12_e9c6_R1_1_I0 /\ Inv24_ed8d_R0_1_I0 /\ Next => Inv24_ed8d_R0_1_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF GrantedVoteSet
  \* (Inv24_ed8d_R0_1_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv24_ed8d_R0_1_I0 /\ RequestVoteAction => Inv24_ed8d_R0_1_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv24_ed8d_R0_1_I0,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(votesGranted[VARI] \in Quorum)) \/ (~(\E INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] = currentTerm[VARI])))'
      BY DEF Inv24_ed8d_R0_1_I0, RequestVoteAction
    <2>1. (((state[VARI] = Candidate /\ VARI # VARJ)) /\ ((votesGranted[VARI] \in Quorum)) => (~(\E INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] = currentTerm[VARI])))'
      <3> SUFFICES ASSUME (((state[VARI] = Candidate /\ VARI # VARJ)) /\ ((votesGranted[VARI] \in Quorum)))'
                   PROVE  (~(\E INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] = currentTerm[VARI]))'
        OBVIOUS
      <3>1. ((\A INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] # currentTerm[VARI]))'
        <4> SUFFICES ASSUME NEW INDK \in (DOMAIN log[VARJ])'
                     PROVE  (log[VARJ][INDK] # currentTerm[VARI])'
          OBVIOUS
        <4>1. CASE (votesGranted[VARI] \in Quorum /\ state[VARI] = Candidate /\ VARI # VARJ)
\*              BY SMTT(1000), <4>1, EmptySeq, TWO_SERVERS_Assumption, LenProperties,ElementOfSeq DEF TypeOK,RequestVoteAction,RequestVote,Inv24_ed8d_R0_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
            <5>1. ~( log[VARJ][INDK] = currentTerm[VARI]) 
                                  BY SMTT(1000), <4>1, EmptySeq, TWO_SERVERS_Assumption, LenProperties,ElementOfSeq DEF TypeOK,RequestVoteAction,RequestVote,Inv24_ed8d_R0_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
            <5>2. ( log[VARJ]' = log[VARJ]) 
                BY SMTT(1000), <4>1, EmptySeq, TWO_SERVERS_Assumption, LenProperties,ElementOfSeq DEF TypeOK,RequestVoteAction,RequestVote,Inv24_ed8d_R0_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
            <5>2a. ~( log'[VARJ][INDK] = currentTerm[VARI]) 
                BY SMTT(1000), <4>1,<5>2,<5>1, EmptySeq, TWO_SERVERS_Assumption, LenProperties,ElementOfSeq DEF TypeOK,RequestVoteAction,RequestVote,Inv24_ed8d_R0_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
            
            <5>3. QED 
                BY SMTT(1000), <5>1, <5>2, <5>2a, <4>1, EmptySeq, TWO_SERVERS_Assumption, LenProperties,ElementOfSeq DEF TypeOK,RequestVoteAction,RequestVote,Inv24_ed8d_R0_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
        <4> QED
          BY SMTT(1000), TWO_SERVERS_Assumption, EmptySeq, LenProperties,ElementOfSeq DEF TypeOK,RequestVoteAction,RequestVote,Inv24_ed8d_R0_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
              
      
      <3> QED
        BY <3>1 DEF TypeOK,RequestVoteAction,RequestVote,Inv24_ed8d_R0_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
          
    
    <2> QED
      BY <2>1 DEF TypeOK,RequestVoteAction,RequestVote,Inv24_ed8d_R0_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv24_ed8d_R0_1_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv24_ed8d_R0_1_I0 /\ UpdateTermAction => Inv24_ed8d_R0_1_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv24_ed8d_R0_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv24_ed8d_R0_1_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv24_ed8d_R0_1_I0 /\ BecomeLeaderAction => Inv24_ed8d_R0_1_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv24_ed8d_R0_1_I0
  \* (Inv24_ed8d_R0_1_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv11_d848_R2_1_I0 /\ Inv24_ed8d_R0_1_I0 /\ ClientRequestAction => Inv24_ed8d_R0_1_I0' BY DEF TypeOK,Inv11_d848_R2_1_I0,ClientRequestAction,ClientRequest,Inv24_ed8d_R0_1_I0
  \* (Inv24_ed8d_R0_1_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv24_ed8d_R0_1_I0 /\ AppendEntriesAction => Inv24_ed8d_R0_1_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv24_ed8d_R0_1_I0
  \* (Inv24_ed8d_R0_1_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv24_ed8d_R0_1_I0 /\ HandleRequestVoteRequestAction => Inv24_ed8d_R0_1_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv24_ed8d_R0_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv24_ed8d_R0_1_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv33_5a2e_R2_2_I0 /\ Inv24_ed8d_R0_1_I0 /\ HandleRequestVoteResponseAction => Inv24_ed8d_R0_1_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv33_5a2e_R2_2_I0,
                        Inv24_ed8d_R0_1_I0,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(votesGranted[VARI] \in Quorum)) \/ (~(\E INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] = currentTerm[VARI])))'
      BY DEF HandleRequestVoteResponseAction, Inv24_ed8d_R0_1_I0
    <2> QED
      BY TWO_SERVERS_Assumption DEF TypeOK,Inv33_5a2e_R2_2_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv24_ed8d_R0_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv24_ed8d_R0_1_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv12_e9c6_R1_1_I0 /\ Inv24_ed8d_R0_1_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv24_ed8d_R0_1_I0' BY DEF TypeOK,Inv12_e9c6_R1_1_I0,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv24_ed8d_R0_1_I0
  \* (Inv24_ed8d_R0_1_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv24_ed8d_R0_1_I0 /\ HandleAppendEntriesResponseAction => Inv24_ed8d_R0_1_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv24_ed8d_R0_1_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv11_d848_R2_1_I0
THEOREM L_5 == TypeOK /\ Inv8_8e53_R5_0_I0 /\ Inv127_0bd2_R5_1_I2 /\ Inv9072_27f5_R5_1_I2 /\ Inv9_42ac_R5_1_I2 /\ Inv8_8e53_R5_0_I0 /\ Inv11_d848_R2_1_I0 /\ Next => Inv11_d848_R2_1_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv11_d848_R2_1_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv11_d848_R2_1_I0 /\ RequestVoteAction => Inv11_d848_R2_1_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv11_d848_R2_1_I0,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) \/ (~((state[VARJ] = Leader))) \/ (~(votesGranted[VARI] \in Quorum)))'
      BY DEF Inv11_d848_R2_1_I0, RequestVoteAction
    <2> QED
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv11_d848_R2_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv11_d848_R2_1_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv11_d848_R2_1_I0 /\ UpdateTermAction => Inv11_d848_R2_1_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv11_d848_R2_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv11_d848_R2_1_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv8_8e53_R5_0_I0 /\ Inv11_d848_R2_1_I0 /\ BecomeLeaderAction => Inv11_d848_R2_1_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv8_8e53_R5_0_I0,
                        Inv11_d848_R2_1_I0,
                        TRUE,
                        NEW i \in Server,
                        BecomeLeader(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) \/ (~((state[VARJ] = Leader))) \/ (~(votesGranted[VARI] \in Quorum)))'
      BY DEF BecomeLeaderAction, Inv11_d848_R2_1_I0
    <2> QED
      BY DEF TypeOK,Inv8_8e53_R5_0_I0,BecomeLeaderAction,BecomeLeader,Inv11_d848_R2_1_I0
  \* (Inv11_d848_R2_1_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv11_d848_R2_1_I0 /\ ClientRequestAction => Inv11_d848_R2_1_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv11_d848_R2_1_I0
  \* (Inv11_d848_R2_1_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv11_d848_R2_1_I0 /\ AppendEntriesAction => Inv11_d848_R2_1_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv11_d848_R2_1_I0
  \* (Inv11_d848_R2_1_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv11_d848_R2_1_I0 /\ HandleRequestVoteRequestAction => Inv11_d848_R2_1_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv11_d848_R2_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv11_d848_R2_1_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv127_0bd2_R5_1_I2 /\ Inv9072_27f5_R5_1_I2 /\ Inv9_42ac_R5_1_I2 /\ Inv8_8e53_R5_0_I0 /\ Inv11_d848_R2_1_I0 /\ HandleRequestVoteResponseAction => Inv11_d848_R2_1_I0' BY DEF TypeOK,Inv127_0bd2_R5_1_I2,Inv9072_27f5_R5_1_I2,Inv9_42ac_R5_1_I2,Inv8_8e53_R5_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv11_d848_R2_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv11_d848_R2_1_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv11_d848_R2_1_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv11_d848_R2_1_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv11_d848_R2_1_I0
  \* (Inv11_d848_R2_1_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv11_d848_R2_1_I0 /\ HandleAppendEntriesResponseAction => Inv11_d848_R2_1_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv11_d848_R2_1_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv8_8e53_R5_0_I0
THEOREM L_6 == TypeOK /\ Inv0_2c32_R8_1_I1 /\ Inv9_42ac_R5_1_I2 /\ Inv8_8e53_R5_0_I0 /\ Next => Inv8_8e53_R5_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv8_8e53_R5_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv0_2c32_R8_1_I1 /\ Inv8_8e53_R5_0_I0 /\ RequestVoteAction => Inv8_8e53_R5_0_I0' BY DEF TypeOK,Inv0_2c32_R8_1_I1,RequestVoteAction,RequestVote,Inv8_8e53_R5_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv8_8e53_R5_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv8_8e53_R5_0_I0 /\ UpdateTermAction => Inv8_8e53_R5_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv8_8e53_R5_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv8_8e53_R5_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv8_8e53_R5_0_I0 /\ BecomeLeaderAction => Inv8_8e53_R5_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv8_8e53_R5_0_I0
  \* (Inv8_8e53_R5_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv8_8e53_R5_0_I0 /\ ClientRequestAction => Inv8_8e53_R5_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv8_8e53_R5_0_I0
  \* (Inv8_8e53_R5_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv8_8e53_R5_0_I0 /\ AppendEntriesAction => Inv8_8e53_R5_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv8_8e53_R5_0_I0
  \* (Inv8_8e53_R5_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv8_8e53_R5_0_I0 /\ HandleRequestVoteRequestAction => Inv8_8e53_R5_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv8_8e53_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv8_8e53_R5_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv9_42ac_R5_1_I2 /\ Inv8_8e53_R5_0_I0 /\ HandleRequestVoteResponseAction => Inv8_8e53_R5_0_I0' BY DEF TypeOK,Inv9_42ac_R5_1_I2,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv8_8e53_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv8_8e53_R5_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv8_8e53_R5_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv8_8e53_R5_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv8_8e53_R5_0_I0
  \* (Inv8_8e53_R5_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv8_8e53_R5_0_I0 /\ HandleAppendEntriesResponseAction => Inv8_8e53_R5_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv8_8e53_R5_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv9_42ac_R5_1_I2
THEOREM L_7 == TypeOK /\ Inv14_f533_R11_2_I0 /\ Inv166_e30e_R11_0_I1 /\ Inv10_82b3_R11_1_I0 /\ Inv9_42ac_R5_1_I2 /\ Next => Inv9_42ac_R5_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv9_42ac_R5_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv14_f533_R11_2_I0 /\ Inv9_42ac_R5_1_I2 /\ RequestVoteAction => Inv9_42ac_R5_1_I2' BY DEF TypeOK,Inv14_f533_R11_2_I0,RequestVoteAction,RequestVote,Inv9_42ac_R5_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv9_42ac_R5_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv9_42ac_R5_1_I2 /\ UpdateTermAction => Inv9_42ac_R5_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv9_42ac_R5_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv9_42ac_R5_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv9_42ac_R5_1_I2 /\ BecomeLeaderAction => Inv9_42ac_R5_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv9_42ac_R5_1_I2
  \* (Inv9_42ac_R5_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv9_42ac_R5_1_I2 /\ ClientRequestAction => Inv9_42ac_R5_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv9_42ac_R5_1_I2
  \* (Inv9_42ac_R5_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv9_42ac_R5_1_I2 /\ AppendEntriesAction => Inv9_42ac_R5_1_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv9_42ac_R5_1_I2
  \* (Inv9_42ac_R5_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv166_e30e_R11_0_I1 /\ Inv9_42ac_R5_1_I2 /\ HandleRequestVoteRequestAction => Inv9_42ac_R5_1_I2' BY DEF TypeOK,Inv166_e30e_R11_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_42ac_R5_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv9_42ac_R5_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv10_82b3_R11_1_I0 /\ Inv9_42ac_R5_1_I2 /\ HandleRequestVoteResponseAction => Inv9_42ac_R5_1_I2' BY DEF TypeOK,Inv10_82b3_R11_1_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv9_42ac_R5_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv9_42ac_R5_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv9_42ac_R5_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv9_42ac_R5_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv9_42ac_R5_1_I2
  \* (Inv9_42ac_R5_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv9_42ac_R5_1_I2 /\ HandleAppendEntriesResponseAction => Inv9_42ac_R5_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv9_42ac_R5_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv166_e30e_R11_0_I1
THEOREM L_8 == TypeOK /\ Inv0_2c32_R8_1_I1 /\ Inv0_2c32_R8_1_I1 /\ Inv0_2c32_R8_1_I1 /\ Inv13_3715_R21_0_I0 /\ Inv13_3715_R21_0_I0 /\ Inv166_e30e_R11_0_I1 /\ Next => Inv166_e30e_R11_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv166_e30e_R11_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv0_2c32_R8_1_I1 /\ Inv166_e30e_R11_0_I1 /\ RequestVoteAction => Inv166_e30e_R11_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv0_2c32_R8_1_I1,
                        Inv166_e30e_R11_0_I1,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server'
                 PROVE  (((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI )) \/ (((state[VARI] = Follower))))'
      BY DEF Inv166_e30e_R11_0_I1, RequestVoteAction
    <2> ((((state[VARI] # Follower))) => ((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI )) )'
      <3> SUFFICES ASSUME (state[VARI] # Follower)',
                          NEW t \in (votesGranted[VARI])'
                   PROVE  (/\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI)'
        OBVIOUS
      <3>1. (currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI)'
        <4> SUFFICES ASSUME (currentTerm[t] = currentTerm[VARI])'
                     PROVE  (votedFor[t] = VARI)'
          OBVIOUS
        <4>1. CASE VARI = t
        BY <4>1 DEF TypeOK,Inv0_2c32_R8_1_I1,Inv0_2c32_R8_1_I1,RequestVoteAction,RequestVote,Inv166_e30e_R11_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
        <4>2. CASE VARI # t /\ VARI = i
        BY <4>2 DEF TypeOK,Inv0_2c32_R8_1_I1,Inv0_2c32_R8_1_I1,RequestVoteAction,RequestVote,Inv166_e30e_R11_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
        <4>3. CASE VARI # t /\ VARI # i /\ currentTerm[VARI] < currentTerm[i] + 1
        BY <4>3 DEF TypeOK,Inv0_2c32_R8_1_I1,Inv0_2c32_R8_1_I1,RequestVoteAction,RequestVote,Inv166_e30e_R11_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
        <4>4. CASE VARI # t /\ VARI # i /\ currentTerm[VARI] >= currentTerm[i] + 1 /\ state[VARI] \notin {Leader, Candidate}
        BY <4>4 DEF TypeOK,Inv0_2c32_R8_1_I1,Inv0_2c32_R8_1_I1,RequestVoteAction,RequestVote,Inv166_e30e_R11_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
        <4>5. CASE VARI # t /\ VARI # i /\ currentTerm[VARI] >= currentTerm[i] + 1 /\ state[VARI] \in {Leader, Candidate}
        BY <4>5 DEF TypeOK,Inv0_2c32_R8_1_I1,Inv0_2c32_R8_1_I1,RequestVoteAction,RequestVote,Inv166_e30e_R11_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5 DEF TypeOK,Inv0_2c32_R8_1_I1,Inv0_2c32_R8_1_I1,RequestVoteAction,RequestVote,Inv166_e30e_R11_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
      <3>2. QED
        BY <3>1
          
    
    <2> QED
      BY DEF TypeOK,Inv0_2c32_R8_1_I1,Inv0_2c32_R8_1_I1,RequestVoteAction,RequestVote,Inv166_e30e_R11_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv166_e30e_R11_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv0_2c32_R8_1_I1 /\ Inv166_e30e_R11_0_I1 /\ UpdateTermAction => Inv166_e30e_R11_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv0_2c32_R8_1_I1,
                        Inv166_e30e_R11_0_I1,
                        TRUE,
                        NEW m \in requestVoteRequestMsgs \cup requestVoteResponseMsgs \cup appendEntriesRequestMsgs \cup appendEntriesResponseMsgs,
                        UpdateTerm(m, m.mterm, m.mdest),
                        NEW VARI \in Server'
                 PROVE  (((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI )) \/ (((state[VARI] = Follower))))'
      BY DEF Inv166_e30e_R11_0_I1, UpdateTermAction    
    <2> QED
      BY FIVE_SERVERS_Assumption DEF TypeOK,Inv0_2c32_R8_1_I1,UpdateTermAction,UpdateTerm,Inv166_e30e_R11_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv166_e30e_R11_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv166_e30e_R11_0_I1 /\ BecomeLeaderAction => Inv166_e30e_R11_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv166_e30e_R11_0_I1
  \* (Inv166_e30e_R11_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv166_e30e_R11_0_I1 /\ ClientRequestAction => Inv166_e30e_R11_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv166_e30e_R11_0_I1
  \* (Inv166_e30e_R11_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv166_e30e_R11_0_I1 /\ AppendEntriesAction => Inv166_e30e_R11_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv166_e30e_R11_0_I1
  \* (Inv166_e30e_R11_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv166_e30e_R11_0_I1 /\ HandleRequestVoteRequestAction => Inv166_e30e_R11_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv166_e30e_R11_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv166_e30e_R11_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv13_3715_R21_0_I0 /\ Inv166_e30e_R11_0_I1 /\ HandleRequestVoteResponseAction => Inv166_e30e_R11_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv13_3715_R21_0_I0,
                        Inv166_e30e_R11_0_I1,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server'
                 PROVE  (((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI )) \/ (((state[VARI] = Follower))))'
      BY DEF HandleRequestVoteResponseAction, Inv166_e30e_R11_0_I1
    <2> ((((state[VARI] # Follower))) => ((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI )) )'
      <3> SUFFICES ASSUME (state[VARI] # Follower)',
                          NEW t \in (votesGranted[VARI])'
                   PROVE  (/\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI)'
        OBVIOUS
      <3>1. (currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI)'
        <4> SUFFICES ASSUME (currentTerm[t] = currentTerm[VARI])'
                     PROVE  (votedFor[t] = VARI)'
          OBVIOUS
         <4> CASE VARI = t
             BY SMTT(30) DEF TypeOK,Inv13_3715_R21_0_I0,Inv13_3715_R21_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv166_e30e_R11_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <4> CASE VARI # t /\ m.mdest = VARI
             BY SMTT(3000), FIVE_SERVERS_Assumption DEF TypeOK,Inv13_3715_R21_0_I0,Inv13_3715_R21_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv166_e30e_R11_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <4>3. CASE VARI # t /\ VARI # m.mdest /\ currentTerm[VARI] < currentTerm[m.mdest] + 1
               BY <4>3 DEF TypeOK,Inv13_3715_R21_0_I0,Inv13_3715_R21_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv166_e30e_R11_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
          <4>4. CASE VARI # t /\ VARI # m.mdest /\ currentTerm[VARI] >= currentTerm[m.mdest] + 1 /\ state[VARI] \notin {Leader, Candidate}
              BY <4>4 DEF TypeOK,Inv13_3715_R21_0_I0,Inv13_3715_R21_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv166_e30e_R11_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
           <4>5. CASE VARI # t /\ VARI # m.mdest /\ currentTerm[VARI] >= currentTerm[m.mdest] + 1 /\ state[VARI] \in {Leader, Candidate}
              BY <4>5 DEF TypeOK,Inv13_3715_R21_0_I0,Inv13_3715_R21_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv166_e30e_R11_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
        
        <4> QED
          BY <4>3, <4>4, <4>5, SMTT(30) DEF TypeOK,Inv13_3715_R21_0_I0,Inv13_3715_R21_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv166_e30e_R11_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
        
      <3>2. QED
        BY <3>1
          
    
    <2> QED
      BY DEF TypeOK,Inv13_3715_R21_0_I0,Inv13_3715_R21_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv166_e30e_R11_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv166_e30e_R11_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv166_e30e_R11_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv166_e30e_R11_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv166_e30e_R11_0_I1
  \* (Inv166_e30e_R11_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv166_e30e_R11_0_I1 /\ HandleAppendEntriesResponseAction => Inv166_e30e_R11_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv166_e30e_R11_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv13_3715_R21_0_I0
THEOREM L_9 == TypeOK /\ Inv14_f533_R11_2_I0 /\ Inv14_f533_R11_2_I0 /\ Inv13_3715_R21_0_I0 /\ Next => Inv13_3715_R21_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv13_3715_R21_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv14_f533_R11_2_I0 /\ Inv13_3715_R21_0_I0 /\ RequestVoteAction => Inv13_3715_R21_0_I0' BY DEF TypeOK,Inv14_f533_R11_2_I0,RequestVoteAction,RequestVote,Inv13_3715_R21_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv13_3715_R21_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv14_f533_R11_2_I0 /\ Inv13_3715_R21_0_I0 /\ UpdateTermAction => Inv13_3715_R21_0_I0' BY DEF TypeOK,Inv14_f533_R11_2_I0,UpdateTermAction,UpdateTerm,Inv13_3715_R21_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv13_3715_R21_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv13_3715_R21_0_I0 /\ BecomeLeaderAction => Inv13_3715_R21_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv13_3715_R21_0_I0
  \* (Inv13_3715_R21_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv13_3715_R21_0_I0 /\ ClientRequestAction => Inv13_3715_R21_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv13_3715_R21_0_I0
  \* (Inv13_3715_R21_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv13_3715_R21_0_I0 /\ AppendEntriesAction => Inv13_3715_R21_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv13_3715_R21_0_I0
  \* (Inv13_3715_R21_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv13_3715_R21_0_I0 /\ HandleRequestVoteRequestAction => Inv13_3715_R21_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv13_3715_R21_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv13_3715_R21_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv13_3715_R21_0_I0 /\ HandleRequestVoteResponseAction => Inv13_3715_R21_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv13_3715_R21_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv13_3715_R21_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv13_3715_R21_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv13_3715_R21_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv13_3715_R21_0_I0
  \* (Inv13_3715_R21_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv13_3715_R21_0_I0 /\ HandleAppendEntriesResponseAction => Inv13_3715_R21_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv13_3715_R21_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv14_f533_R11_2_I0
THEOREM L_10 == TypeOK /\ Inv14_f533_R11_2_I0 /\ Next => Inv14_f533_R11_2_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv14_f533_R11_2_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv14_f533_R11_2_I0 /\ RequestVoteAction => Inv14_f533_R11_2_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv14_f533_R11_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv14_f533_R11_2_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv14_f533_R11_2_I0 /\ UpdateTermAction => Inv14_f533_R11_2_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv14_f533_R11_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv14_f533_R11_2_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv14_f533_R11_2_I0 /\ BecomeLeaderAction => Inv14_f533_R11_2_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv14_f533_R11_2_I0
  \* (Inv14_f533_R11_2_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv14_f533_R11_2_I0 /\ ClientRequestAction => Inv14_f533_R11_2_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv14_f533_R11_2_I0
  \* (Inv14_f533_R11_2_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv14_f533_R11_2_I0 /\ AppendEntriesAction => Inv14_f533_R11_2_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv14_f533_R11_2_I0
  \* (Inv14_f533_R11_2_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv14_f533_R11_2_I0 /\ HandleRequestVoteRequestAction => Inv14_f533_R11_2_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv14_f533_R11_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv14_f533_R11_2_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv14_f533_R11_2_I0 /\ HandleRequestVoteResponseAction => Inv14_f533_R11_2_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv14_f533_R11_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv14_f533_R11_2_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv14_f533_R11_2_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv14_f533_R11_2_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv14_f533_R11_2_I0
  \* (Inv14_f533_R11_2_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv14_f533_R11_2_I0 /\ HandleAppendEntriesResponseAction => Inv14_f533_R11_2_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv14_f533_R11_2_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv0_2c32_R8_1_I1
THEOREM L_11 == TypeOK /\ Inv14_f533_R11_2_I0 /\ Inv0_2c32_R8_1_I1 /\ Next => Inv0_2c32_R8_1_I1'
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
  <1>7. TypeOK /\ Inv14_f533_R11_2_I0 /\ Inv0_2c32_R8_1_I1 /\ HandleRequestVoteResponseAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,Inv14_f533_R11_2_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv0_2c32_R8_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_2c32_R8_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv0_2c32_R8_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv0_2c32_R8_1_I1
  \* (Inv0_2c32_R8_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv0_2c32_R8_1_I1 /\ HandleAppendEntriesResponseAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv0_2c32_R8_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv10_82b3_R11_1_I0
THEOREM L_12 == TypeOK /\ Inv13_3715_R21_0_I0 /\ Inv10_82b3_R11_1_I0 /\ Next => Inv10_82b3_R11_1_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv10_82b3_R11_1_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv10_82b3_R11_1_I0 /\ RequestVoteAction => Inv10_82b3_R11_1_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv10_82b3_R11_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10_82b3_R11_1_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv10_82b3_R11_1_I0 /\ UpdateTermAction => Inv10_82b3_R11_1_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv10_82b3_R11_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10_82b3_R11_1_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv10_82b3_R11_1_I0 /\ BecomeLeaderAction => Inv10_82b3_R11_1_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv10_82b3_R11_1_I0
  \* (Inv10_82b3_R11_1_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv10_82b3_R11_1_I0 /\ ClientRequestAction => Inv10_82b3_R11_1_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv10_82b3_R11_1_I0
  \* (Inv10_82b3_R11_1_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv10_82b3_R11_1_I0 /\ AppendEntriesAction => Inv10_82b3_R11_1_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv10_82b3_R11_1_I0
  \* (Inv10_82b3_R11_1_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv13_3715_R21_0_I0 /\ Inv10_82b3_R11_1_I0 /\ HandleRequestVoteRequestAction => Inv10_82b3_R11_1_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv13_3715_R21_0_I0,
                        Inv10_82b3_R11_1_I0,
                        NEW m \in requestVoteRequestMsgs,
                        HandleRequestVoteRequest(m),
                        NEW mi \in requestVoteResponseMsgs', NEW mj \in requestVoteResponseMsgs',
                        (/\ mi.mterm = mj.mterm /\ mi.msource = mj.msource /\ mi.mvoteGranted /\ mj.mvoteGranted)'
                 PROVE  (mi.mdest = mj.mdest)'
      BY DEF HandleRequestVoteRequestAction, Inv10_82b3_R11_1_I0
    <2>1 CASE m.mterm # currentTerm[m.mdest]
          BY <2>1 DEF TypeOK,Inv13_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_82b3_R11_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>2. CASE m.mterm = currentTerm[m.mdest] /\ votedFor[m.mdest] \notin {Nil, m.msource}
          BY <2>2 DEF TypeOK,Inv13_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_82b3_R11_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>3. CASE m.mterm = currentTerm[m.mdest] /\ votedFor[m.mdest] \in {Nil, m.msource}
        <3>1. CASE m.mdest # mi.msource
            BY <2>3, <3>1 DEF TypeOK,Inv13_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_82b3_R11_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         \* m is the vote request message so its dest is the one receivign the vote request.         
         <3>2. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] # mi.mterm
            BY <2>3, <3>2 DEF TypeOK,Inv13_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_82b3_R11_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>3. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest # mi.msource
            BY <2>3, <3>3 DEF TypeOK,Inv13_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_82b3_R11_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>4. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest = mi.msource /\ mi \in requestVoteResponseMsgs
            <4>1. currentTerm[mi.msource] = mi.mterm /\ mi.mvoteGranted
                BY <2>3, <3>4 DEF TypeOK,Inv13_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_82b3_R11_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>2. votedFor[mi.msource] = mi.mdest
                BY  <4>1, <2>3,<3>4 DEF TypeOK,Inv13_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_82b3_R11_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. QED 
                BY <4>1, <4>2,<3>4,<2>3 DEF TypeOK,Inv13_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_82b3_R11_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>5. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest = mi.msource /\ mi \notin requestVoteResponseMsgs /\ mj \notin requestVoteResponseMsgs
            <4>1. currentTerm[mi.msource] = mi.mterm /\ mi.mvoteGranted
              BY <2>3, <3>5 DEF TypeOK,Inv13_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_82b3_R11_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. QED 
              BY <2>3, <3>5, <4>1 DEF TypeOK,Inv13_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_82b3_R11_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>6. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest = mi.msource /\ mi \notin requestVoteResponseMsgs /\ mj \in requestVoteResponseMsgs
            <4>1. currentTerm[mj.msource] = mj.mterm /\ mj.mvoteGranted
               BY <2>3, <3>6 DEF TypeOK,Inv13_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_82b3_R11_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>2. votedFor[mj.msource] = mj.mdest
               BY <2>3, <4>1, <3>6 DEF TypeOK,Inv13_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_82b3_R11_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. QED 
              BY <4>1,<4>2, <3>6 DEF TypeOK,Inv13_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_82b3_R11_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            
         <3>. QED BY <3>1, <3>2, <3>3,<3>4,<3>5,<3>6    
    <2> QED
      BY <2>1, <2>2, <2>3 DEF TypeOK,Inv13_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_82b3_R11_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_82b3_R11_1_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv10_82b3_R11_1_I0 /\ HandleRequestVoteResponseAction => Inv10_82b3_R11_1_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv10_82b3_R11_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_82b3_R11_1_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv10_82b3_R11_1_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv10_82b3_R11_1_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv10_82b3_R11_1_I0
  \* (Inv10_82b3_R11_1_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv10_82b3_R11_1_I0 /\ HandleAppendEntriesResponseAction => Inv10_82b3_R11_1_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv10_82b3_R11_1_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv127_0bd2_R5_1_I2
THEOREM L_13 == TypeOK /\ Inv2513_1e2e_R6_3_I1 /\ Inv61_fe26_R9_0_I1 /\ Inv127_0bd2_R5_1_I2 /\ Next => Inv127_0bd2_R5_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF GrantedVoteSet
  \* (Inv127_0bd2_R5_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv127_0bd2_R5_1_I2 /\ RequestVoteAction => Inv127_0bd2_R5_1_I2' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv127_0bd2_R5_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv127_0bd2_R5_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv2513_1e2e_R6_3_I1 /\ Inv127_0bd2_R5_1_I2 /\ UpdateTermAction => Inv127_0bd2_R5_1_I2' BY DEF TypeOK,Inv2513_1e2e_R6_3_I1,UpdateTermAction,UpdateTerm,Inv127_0bd2_R5_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv127_0bd2_R5_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv127_0bd2_R5_1_I2 /\ BecomeLeaderAction => Inv127_0bd2_R5_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv127_0bd2_R5_1_I2
  \* (Inv127_0bd2_R5_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv127_0bd2_R5_1_I2 /\ ClientRequestAction => Inv127_0bd2_R5_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv127_0bd2_R5_1_I2
  \* (Inv127_0bd2_R5_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv127_0bd2_R5_1_I2 /\ AppendEntriesAction => Inv127_0bd2_R5_1_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv127_0bd2_R5_1_I2
  \* (Inv127_0bd2_R5_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv61_fe26_R9_0_I1 /\ Inv127_0bd2_R5_1_I2 /\ HandleRequestVoteRequestAction => Inv127_0bd2_R5_1_I2' BY DEF TypeOK,Inv61_fe26_R9_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv127_0bd2_R5_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv127_0bd2_R5_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv127_0bd2_R5_1_I2 /\ HandleRequestVoteResponseAction => Inv127_0bd2_R5_1_I2' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv127_0bd2_R5_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv127_0bd2_R5_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv127_0bd2_R5_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv127_0bd2_R5_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv127_0bd2_R5_1_I2
  \* (Inv127_0bd2_R5_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv127_0bd2_R5_1_I2 /\ HandleAppendEntriesResponseAction => Inv127_0bd2_R5_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv127_0bd2_R5_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv61_fe26_R9_0_I1
THEOREM L_14 == TypeOK /\ Inv61_fe26_R9_0_I1 /\ Next => Inv61_fe26_R9_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv61_fe26_R9_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv61_fe26_R9_0_I1 /\ RequestVoteAction => Inv61_fe26_R9_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv61_fe26_R9_0_I1,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARREQVM \in requestVoteRequestMsgs'
                 PROVE  (~(VARREQVM.msource = VARI) \/ (~(votesGranted[VARI] = {})))'
      BY DEF Inv61_fe26_R9_0_I1, RequestVoteAction
    <2> CASE VARI = i
          BY FS_Difference, FS_Subset DEF LastTerm, TypeOK,RequestVoteAction,RequestVote,Inv61_fe26_R9_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2> CASE VARI # i
          BY FS_Difference, FS_Subset DEF LastTerm, TypeOK,RequestVoteAction,RequestVote,Inv61_fe26_R9_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType        
    <2> QED
      BY FS_Difference, FS_Subset DEF LastTerm, TypeOK,RequestVoteAction,RequestVote,Inv61_fe26_R9_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv61_fe26_R9_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv61_fe26_R9_0_I1 /\ UpdateTermAction => Inv61_fe26_R9_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv61_fe26_R9_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv61_fe26_R9_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv61_fe26_R9_0_I1 /\ BecomeLeaderAction => Inv61_fe26_R9_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv61_fe26_R9_0_I1
  \* (Inv61_fe26_R9_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv61_fe26_R9_0_I1 /\ ClientRequestAction => Inv61_fe26_R9_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv61_fe26_R9_0_I1
  \* (Inv61_fe26_R9_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv61_fe26_R9_0_I1 /\ AppendEntriesAction => Inv61_fe26_R9_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv61_fe26_R9_0_I1
  \* (Inv61_fe26_R9_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv61_fe26_R9_0_I1 /\ HandleRequestVoteRequestAction => Inv61_fe26_R9_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv61_fe26_R9_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv61_fe26_R9_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv61_fe26_R9_0_I1 /\ HandleRequestVoteResponseAction => Inv61_fe26_R9_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv61_fe26_R9_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv61_fe26_R9_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv61_fe26_R9_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv61_fe26_R9_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv61_fe26_R9_0_I1
  \* (Inv61_fe26_R9_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv61_fe26_R9_0_I1 /\ HandleAppendEntriesResponseAction => Inv61_fe26_R9_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv61_fe26_R9_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv2513_1e2e_R6_3_I1
THEOREM L_15 == TypeOK /\ Inv12_9e78_R16_0_I0 /\ Inv2513_1e2e_R6_3_I1 /\ Next => Inv2513_1e2e_R6_3_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv2513_1e2e_R6_3_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv2513_1e2e_R6_3_I1 /\ RequestVoteAction => Inv2513_1e2e_R6_3_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv2513_1e2e_R6_3_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv2513_1e2e_R6_3_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv2513_1e2e_R6_3_I1 /\ UpdateTermAction => Inv2513_1e2e_R6_3_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv2513_1e2e_R6_3_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv2513_1e2e_R6_3_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv2513_1e2e_R6_3_I1 /\ BecomeLeaderAction => Inv2513_1e2e_R6_3_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv2513_1e2e_R6_3_I1
  \* (Inv2513_1e2e_R6_3_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv2513_1e2e_R6_3_I1 /\ ClientRequestAction => Inv2513_1e2e_R6_3_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv2513_1e2e_R6_3_I1
  \* (Inv2513_1e2e_R6_3_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv2513_1e2e_R6_3_I1 /\ AppendEntriesAction => Inv2513_1e2e_R6_3_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv2513_1e2e_R6_3_I1
  \* (Inv2513_1e2e_R6_3_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv12_9e78_R16_0_I0 /\ Inv2513_1e2e_R6_3_I1 /\ HandleRequestVoteRequestAction => Inv2513_1e2e_R6_3_I1' BY DEF TypeOK,Inv12_9e78_R16_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv2513_1e2e_R6_3_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv2513_1e2e_R6_3_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv2513_1e2e_R6_3_I1 /\ HandleRequestVoteResponseAction => Inv2513_1e2e_R6_3_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv2513_1e2e_R6_3_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv2513_1e2e_R6_3_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv2513_1e2e_R6_3_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv2513_1e2e_R6_3_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv2513_1e2e_R6_3_I1
  \* (Inv2513_1e2e_R6_3_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv2513_1e2e_R6_3_I1 /\ HandleAppendEntriesResponseAction => Inv2513_1e2e_R6_3_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv2513_1e2e_R6_3_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv12_9e78_R16_0_I0
THEOREM L_16 == TypeOK /\ Inv12_9e78_R16_0_I0 /\ Next => Inv12_9e78_R16_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv12_9e78_R16_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv12_9e78_R16_0_I0 /\ RequestVoteAction => Inv12_9e78_R16_0_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv12_9e78_R16_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv12_9e78_R16_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv12_9e78_R16_0_I0 /\ UpdateTermAction => Inv12_9e78_R16_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv12_9e78_R16_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv12_9e78_R16_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv12_9e78_R16_0_I0 /\ BecomeLeaderAction => Inv12_9e78_R16_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv12_9e78_R16_0_I0
  \* (Inv12_9e78_R16_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv12_9e78_R16_0_I0 /\ ClientRequestAction => Inv12_9e78_R16_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv12_9e78_R16_0_I0
  \* (Inv12_9e78_R16_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv12_9e78_R16_0_I0 /\ AppendEntriesAction => Inv12_9e78_R16_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv12_9e78_R16_0_I0
  \* (Inv12_9e78_R16_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv12_9e78_R16_0_I0 /\ HandleRequestVoteRequestAction => Inv12_9e78_R16_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv12_9e78_R16_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv12_9e78_R16_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv12_9e78_R16_0_I0 /\ HandleRequestVoteResponseAction => Inv12_9e78_R16_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv12_9e78_R16_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv12_9e78_R16_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv12_9e78_R16_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv12_9e78_R16_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv12_9e78_R16_0_I0
  \* (Inv12_9e78_R16_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv12_9e78_R16_0_I0 /\ HandleAppendEntriesResponseAction => Inv12_9e78_R16_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv12_9e78_R16_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv9072_27f5_R5_1_I2
THEOREM L_17 == TypeOK /\ Inv9072_27f5_R5_1_I2 /\ Next => Inv9072_27f5_R5_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv9072_27f5_R5_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv9072_27f5_R5_1_I2 /\ RequestVoteAction => Inv9072_27f5_R5_1_I2' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv9072_27f5_R5_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv9072_27f5_R5_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv9072_27f5_R5_1_I2 /\ UpdateTermAction => Inv9072_27f5_R5_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv9072_27f5_R5_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv9072_27f5_R5_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv9072_27f5_R5_1_I2 /\ BecomeLeaderAction => Inv9072_27f5_R5_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv9072_27f5_R5_1_I2
  \* (Inv9072_27f5_R5_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv9072_27f5_R5_1_I2 /\ ClientRequestAction => Inv9072_27f5_R5_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv9072_27f5_R5_1_I2
  \* (Inv9072_27f5_R5_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv9072_27f5_R5_1_I2 /\ AppendEntriesAction => Inv9072_27f5_R5_1_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv9072_27f5_R5_1_I2
  \* (Inv9072_27f5_R5_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv9072_27f5_R5_1_I2 /\ HandleRequestVoteRequestAction => Inv9072_27f5_R5_1_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9072_27f5_R5_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv9072_27f5_R5_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv9072_27f5_R5_1_I2 /\ HandleRequestVoteResponseAction => Inv9072_27f5_R5_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv9072_27f5_R5_1_I2,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (((state[VARJ] = Follower)) \/ ((votesGranted[VARI] \in Quorum)) \/ (~((state[VARI] = Leader))))'
      BY DEF HandleRequestVoteResponseAction, Inv9072_27f5_R5_1_I2
    <2> QED
      BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv9072_27f5_R5_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv9072_27f5_R5_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv9072_27f5_R5_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv9072_27f5_R5_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv9072_27f5_R5_1_I2
  \* (Inv9072_27f5_R5_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv9072_27f5_R5_1_I2 /\ HandleAppendEntriesResponseAction => Inv9072_27f5_R5_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv9072_27f5_R5_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv33_5a2e_R2_2_I0
THEOREM L_18 == TypeOK /\ Inv2513_1e2e_R6_3_I1 /\ Inv11_d848_R2_1_I0 /\ Inv82_3acc_R6_1_I1 /\ Inv8_8e53_R5_0_I0 /\ Inv9_42ac_R5_1_I2 /\ Inv789_4aa6_R6_2_I1 /\ Inv1281_1f30_R6_2_I1 /\ Inv4_c57a_R6_2_I1 /\ Inv15967_602c_R4_1_I2 /\ Inv33_5a2e_R2_2_I0 /\ Next => Inv33_5a2e_R2_2_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF GrantedVoteSet
  \* (Inv33_5a2e_R2_2_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv2513_1e2e_R6_3_I1 /\ Inv33_5a2e_R2_2_I0 /\ RequestVoteAction => Inv33_5a2e_R2_2_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv2513_1e2e_R6_3_I1,
                        Inv33_5a2e_R2_2_I0,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(\E INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] = currentTerm[VARI])) \/ (~(GrantedVoteSet(VARI) \in Quorum /\ votesGranted = votesGranted /\ requestVoteResponseMsgs = requestVoteResponseMsgs)))'
      BY DEF Inv33_5a2e_R2_2_I0, RequestVoteAction
    <2> QED
      BY DEF TypeOK,Inv2513_1e2e_R6_3_I1,RequestVoteAction,RequestVote,Inv33_5a2e_R2_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv33_5a2e_R2_2_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv33_5a2e_R2_2_I0 /\ UpdateTermAction => Inv33_5a2e_R2_2_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv33_5a2e_R2_2_I0,
                        TRUE,
                        NEW m \in requestVoteRequestMsgs \cup requestVoteResponseMsgs \cup appendEntriesRequestMsgs \cup appendEntriesResponseMsgs,
                        UpdateTerm(m, m.mterm, m.mdest),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(\E INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] = currentTerm[VARI])) \/ (~(GrantedVoteSet(VARI) \in Quorum /\ votesGranted = votesGranted /\ requestVoteResponseMsgs = requestVoteResponseMsgs)))'
      BY DEF Inv33_5a2e_R2_2_I0, UpdateTermAction
    <2> QED
      BY SMTT(3000),THREE_SERVERS_Assumption DEF TypeOK,UpdateTermAction,UpdateTerm,Inv33_5a2e_R2_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv33_5a2e_R2_2_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv33_5a2e_R2_2_I0 /\ BecomeLeaderAction => Inv33_5a2e_R2_2_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv33_5a2e_R2_2_I0
  \* (Inv33_5a2e_R2_2_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv11_d848_R2_1_I0 /\ Inv82_3acc_R6_1_I1 /\ Inv8_8e53_R5_0_I0 /\ Inv9_42ac_R5_1_I2 /\ Inv33_5a2e_R2_2_I0 /\ ClientRequestAction => Inv33_5a2e_R2_2_I0' BY DEF TypeOK,Inv11_d848_R2_1_I0,Inv82_3acc_R6_1_I1,Inv8_8e53_R5_0_I0,Inv9_42ac_R5_1_I2,ClientRequestAction,ClientRequest,Inv33_5a2e_R2_2_I0
  \* (Inv33_5a2e_R2_2_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv33_5a2e_R2_2_I0 /\ AppendEntriesAction => Inv33_5a2e_R2_2_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv33_5a2e_R2_2_I0
  \* (Inv33_5a2e_R2_2_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv789_4aa6_R6_2_I1 /\ Inv1281_1f30_R6_2_I1 /\ Inv4_c57a_R6_2_I1 /\ Inv33_5a2e_R2_2_I0 /\ HandleRequestVoteRequestAction => Inv33_5a2e_R2_2_I0' BY DEF TypeOK,Inv789_4aa6_R6_2_I1,Inv1281_1f30_R6_2_I1,Inv4_c57a_R6_2_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv33_5a2e_R2_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv33_5a2e_R2_2_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv33_5a2e_R2_2_I0 /\ HandleRequestVoteResponseAction => Inv33_5a2e_R2_2_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv33_5a2e_R2_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv33_5a2e_R2_2_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv15967_602c_R4_1_I2 /\ Inv33_5a2e_R2_2_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv33_5a2e_R2_2_I0' BY DEF TypeOK,Inv15967_602c_R4_1_I2,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv33_5a2e_R2_2_I0
  \* (Inv33_5a2e_R2_2_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv33_5a2e_R2_2_I0 /\ HandleAppendEntriesResponseAction => Inv33_5a2e_R2_2_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv33_5a2e_R2_2_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv15967_602c_R4_1_I2
THEOREM L_19 == TypeOK /\ Inv2513_1e2e_R6_3_I1 /\ Inv33_5a2e_R2_2_I0 /\ Inv789_4aa6_R6_2_I1 /\ Inv4_c57a_R6_2_I1 /\ Inv7_8db7_R7_1_I1 /\ Inv1281_1f30_R6_2_I1 /\ Inv173_650b_R7_1_I1 /\ Inv15967_602c_R4_1_I2 /\ Next => Inv15967_602c_R4_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF GrantedVoteSet
  \* (Inv15967_602c_R4_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv2513_1e2e_R6_3_I1 /\ Inv15967_602c_R4_1_I2 /\ RequestVoteAction => Inv15967_602c_R4_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv2513_1e2e_R6_3_I1,
                        Inv15967_602c_R4_1_I2,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server',
                        NEW VARMAEREQ \in appendEntriesRequestMsgs'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(GrantedVoteSet(VARI) \in Quorum /\ votesGranted = votesGranted /\ requestVoteResponseMsgs = requestVoteResponseMsgs)) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI])))'
      BY DEF Inv15967_602c_R4_1_I2, RequestVoteAction
    <2> QED
      BY DEF TypeOK,Inv2513_1e2e_R6_3_I1,RequestVoteAction,RequestVote,Inv15967_602c_R4_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv15967_602c_R4_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv15967_602c_R4_1_I2 /\ UpdateTermAction => Inv15967_602c_R4_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv15967_602c_R4_1_I2,
                        TRUE,
                        NEW m \in requestVoteRequestMsgs \cup requestVoteResponseMsgs \cup appendEntriesRequestMsgs \cup appendEntriesResponseMsgs,
                        UpdateTerm(m, m.mterm, m.mdest),
                        NEW VARI \in Server',
                        NEW VARJ \in Server',
                        NEW VARMAEREQ \in appendEntriesRequestMsgs'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(GrantedVoteSet(VARI) \in Quorum /\ votesGranted = votesGranted /\ requestVoteResponseMsgs = requestVoteResponseMsgs)) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI])))'
      BY DEF Inv15967_602c_R4_1_I2, UpdateTermAction
    <2> QED
      BY SMTT(300), THREE_SERVERS_Assumption DEF TypeOK,UpdateTermAction,UpdateTerm,Inv15967_602c_R4_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv15967_602c_R4_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv15967_602c_R4_1_I2 /\ BecomeLeaderAction => Inv15967_602c_R4_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv15967_602c_R4_1_I2
  \* (Inv15967_602c_R4_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv15967_602c_R4_1_I2 /\ ClientRequestAction => Inv15967_602c_R4_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv15967_602c_R4_1_I2,
                        TRUE,
                        NEW i \in Server,
                        ClientRequest(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server',
                        NEW VARMAEREQ \in appendEntriesRequestMsgs'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(GrantedVoteSet(VARI) \in Quorum /\ votesGranted = votesGranted /\ requestVoteResponseMsgs = requestVoteResponseMsgs)) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI])))'
      BY DEF ClientRequestAction, Inv15967_602c_R4_1_I2
    <2> QED
      BY SMTT(300),SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq DEF TypeOK,ClientRequestAction,ClientRequest,Inv15967_602c_R4_1_I2, RequestVoteResponseType,RequestVoteRequestType,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv15967_602c_R4_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv33_5a2e_R2_2_I0 /\ Inv15967_602c_R4_1_I2 /\ AppendEntriesAction => Inv15967_602c_R4_1_I2' BY DEF TypeOK,Inv33_5a2e_R2_2_I0,AppendEntriesAction,AppendEntries,Inv15967_602c_R4_1_I2
  \* (Inv15967_602c_R4_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv789_4aa6_R6_2_I1 /\ Inv4_c57a_R6_2_I1 /\ Inv7_8db7_R7_1_I1 /\ Inv1281_1f30_R6_2_I1 /\ Inv173_650b_R7_1_I1 /\ Inv15967_602c_R4_1_I2 /\ HandleRequestVoteRequestAction => Inv15967_602c_R4_1_I2' BY DEF TypeOK,Inv789_4aa6_R6_2_I1,Inv4_c57a_R6_2_I1,Inv7_8db7_R7_1_I1,Inv1281_1f30_R6_2_I1,Inv173_650b_R7_1_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv15967_602c_R4_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv15967_602c_R4_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv15967_602c_R4_1_I2 /\ HandleRequestVoteResponseAction => Inv15967_602c_R4_1_I2' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv15967_602c_R4_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv15967_602c_R4_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv15967_602c_R4_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv15967_602c_R4_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv15967_602c_R4_1_I2
  \* (Inv15967_602c_R4_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv15967_602c_R4_1_I2 /\ HandleAppendEntriesResponseAction => Inv15967_602c_R4_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv15967_602c_R4_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv789_4aa6_R6_2_I1
THEOREM L_20 == TypeOK /\ Inv1281_1f30_R6_2_I1 /\ Inv789_4aa6_R6_2_I1 /\ Next => Inv789_4aa6_R6_2_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv789_4aa6_R6_2_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv1281_1f30_R6_2_I1 /\ Inv789_4aa6_R6_2_I1 /\ RequestVoteAction => Inv789_4aa6_R6_2_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv1281_1f30_R6_2_I1,
                        Inv789_4aa6_R6_2_I1,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server'
                 PROVE  (((state[VARI] = Follower)) \/ ((votedFor[VARI] # Nil /\ VARI \in votesGranted[votedFor[VARI]])))'
      BY DEF Inv789_4aa6_R6_2_I1, RequestVoteAction
    <2> QED
      BY DEF TypeOK,Inv1281_1f30_R6_2_I1,RequestVoteAction,RequestVote,Inv789_4aa6_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv789_4aa6_R6_2_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv789_4aa6_R6_2_I1 /\ UpdateTermAction => Inv789_4aa6_R6_2_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv789_4aa6_R6_2_I1,
                        TRUE,
                        NEW m \in requestVoteRequestMsgs \cup requestVoteResponseMsgs \cup appendEntriesRequestMsgs \cup appendEntriesResponseMsgs,
                        UpdateTerm(m, m.mterm, m.mdest),
                        NEW VARI \in Server'
                 PROVE  (((state[VARI] = Follower)) \/ ((votedFor[VARI] # Nil /\ VARI \in votesGranted[votedFor[VARI]])))'
      BY DEF Inv789_4aa6_R6_2_I1, UpdateTermAction
    <2> QED
      BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv789_4aa6_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv789_4aa6_R6_2_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv789_4aa6_R6_2_I1 /\ BecomeLeaderAction => Inv789_4aa6_R6_2_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv789_4aa6_R6_2_I1
  \* (Inv789_4aa6_R6_2_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv789_4aa6_R6_2_I1 /\ ClientRequestAction => Inv789_4aa6_R6_2_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv789_4aa6_R6_2_I1
  \* (Inv789_4aa6_R6_2_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv789_4aa6_R6_2_I1 /\ AppendEntriesAction => Inv789_4aa6_R6_2_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv789_4aa6_R6_2_I1
  \* (Inv789_4aa6_R6_2_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv789_4aa6_R6_2_I1 /\ HandleRequestVoteRequestAction => Inv789_4aa6_R6_2_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv789_4aa6_R6_2_I1,
                        NEW m \in requestVoteRequestMsgs,
                        HandleRequestVoteRequest(m),
                        NEW VARI \in Server'
                 PROVE  (((state[VARI] = Follower)) \/ ((votedFor[VARI] # Nil /\ VARI \in votesGranted[votedFor[VARI]])))'
      BY DEF HandleRequestVoteRequestAction, Inv789_4aa6_R6_2_I1
    <2> QED
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv789_4aa6_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv789_4aa6_R6_2_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv789_4aa6_R6_2_I1 /\ HandleRequestVoteResponseAction => Inv789_4aa6_R6_2_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv789_4aa6_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv789_4aa6_R6_2_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv789_4aa6_R6_2_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv789_4aa6_R6_2_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv789_4aa6_R6_2_I1
  \* (Inv789_4aa6_R6_2_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv789_4aa6_R6_2_I1 /\ HandleAppendEntriesResponseAction => Inv789_4aa6_R6_2_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv789_4aa6_R6_2_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv1281_1f30_R6_2_I1
THEOREM L_21 == TypeOK /\ Inv1281_1f30_R6_2_I1 /\ Next => Inv1281_1f30_R6_2_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv1281_1f30_R6_2_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv1281_1f30_R6_2_I1 /\ RequestVoteAction => Inv1281_1f30_R6_2_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv1281_1f30_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1281_1f30_R6_2_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv1281_1f30_R6_2_I1 /\ UpdateTermAction => Inv1281_1f30_R6_2_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv1281_1f30_R6_2_I1,
                        TRUE,
                        NEW m \in requestVoteRequestMsgs \cup requestVoteResponseMsgs \cup appendEntriesRequestMsgs \cup appendEntriesResponseMsgs,
                        UpdateTerm(m, m.mterm, m.mdest),
                        NEW VARJ \in Server'
                 PROVE  (((state[VARJ] = Follower)) \/ ((votedFor[VARJ] = VARJ)))'
      BY DEF Inv1281_1f30_R6_2_I1, UpdateTermAction
    <2> QED
      BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv1281_1f30_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1281_1f30_R6_2_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv1281_1f30_R6_2_I1 /\ BecomeLeaderAction => Inv1281_1f30_R6_2_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv1281_1f30_R6_2_I1
  \* (Inv1281_1f30_R6_2_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv1281_1f30_R6_2_I1 /\ ClientRequestAction => Inv1281_1f30_R6_2_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv1281_1f30_R6_2_I1
  \* (Inv1281_1f30_R6_2_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv1281_1f30_R6_2_I1 /\ AppendEntriesAction => Inv1281_1f30_R6_2_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv1281_1f30_R6_2_I1
  \* (Inv1281_1f30_R6_2_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv1281_1f30_R6_2_I1 /\ HandleRequestVoteRequestAction => Inv1281_1f30_R6_2_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv1281_1f30_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1281_1f30_R6_2_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv1281_1f30_R6_2_I1 /\ HandleRequestVoteResponseAction => Inv1281_1f30_R6_2_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv1281_1f30_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1281_1f30_R6_2_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv1281_1f30_R6_2_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv1281_1f30_R6_2_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv1281_1f30_R6_2_I1
  \* (Inv1281_1f30_R6_2_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv1281_1f30_R6_2_I1 /\ HandleAppendEntriesResponseAction => Inv1281_1f30_R6_2_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv1281_1f30_R6_2_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv4_c57a_R6_2_I1
THEOREM L_22 == TypeOK /\ Inv166_e30e_R11_0_I1 /\ Inv40_6261_R15_1_I1 /\ Inv82_3acc_R6_1_I1 /\ Inv0_2c32_R8_1_I1 /\ Inv1281_1f30_R6_2_I1 /\ Inv14_f533_R11_2_I0 /\ Inv363_d176_R15_2_I1 /\ Inv8_2014_R15_0_I0 /\ Inv0_33b0_R0_0_I0 /\ Inv4_c57a_R6_2_I1 /\ Next => Inv4_c57a_R6_2_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF H_LogEntryInTermImpliesSafeAtTerm
  \* (Inv4_c57a_R6_2_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv4_c57a_R6_2_I1 /\ RequestVoteAction => Inv4_c57a_R6_2_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv4_c57a_R6_2_I1,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i)
                 PROVE  Inv4_c57a_R6_2_I1'
      BY DEF RequestVoteAction
    <2>1. H_LogEntryInTermImpliesSafeAtTerm'
      <3> SUFFICES ASSUME NEW s \in Server',
                          NEW i_1 \in (DOMAIN log[s])'
                   PROVE  (  \E Q \in Quorum : 
                           \E u \in Server : 
                               /\ currentTerm[u] >= log[s][i_1]
                               /\ (currentTerm[u] = log[s][i_1]) => (state[u] = Leader /\ votesGranted[u] = Q)
                               /\ \A n \in Q : 
                                   /\ currentTerm[n] >= log[s][i_1]
                                   /\ currentTerm[n] = log[s][i_1] => (votedFor[n] = u))'
        BY DEF H_LogEntryInTermImpliesSafeAtTerm
      <3> QED
        BY SMTT(3000),TWO_SERVERS_Assumption DEF TypeOK,RequestVoteAction,RequestVote,Inv4_c57a_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
      
    <2>2. (currentTerm = currentTerm)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv4_c57a_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>3. (state = state)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv4_c57a_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>4. (log = log)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv4_c57a_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>5. (votedFor = votedFor)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv4_c57a_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>6. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Inv4_c57a_R6_2_I1
  \* (Inv4_c57a_R6_2_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv4_c57a_R6_2_I1 /\ UpdateTermAction => Inv4_c57a_R6_2_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv4_c57a_R6_2_I1,
                        TRUE,
                        NEW m \in requestVoteRequestMsgs \cup requestVoteResponseMsgs \cup appendEntriesRequestMsgs \cup appendEntriesResponseMsgs,
                        UpdateTerm(m, m.mterm, m.mdest)
                 PROVE  Inv4_c57a_R6_2_I1'
      BY DEF UpdateTermAction
    <2>1. H_LogEntryInTermImpliesSafeAtTerm'
      <3> SUFFICES ASSUME NEW s \in Server',
                          NEW i \in (DOMAIN log[s])'
                   PROVE  (\E Q \in Quorum : 
                           \E u \in Server : 
                               /\ currentTerm[u] >= log[s][i]
                               /\ (currentTerm[u] = log[s][i]) => (state[u] = Leader /\ votesGranted[u] = Q)
                               /\ \A n \in Q : 
                                   /\ currentTerm[n] >= log[s][i]
                                   /\ currentTerm[n] = log[s][i] => (votedFor[n] = u))'
        BY DEF H_LogEntryInTermImpliesSafeAtTerm
      <3> QED
        BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv4_c57a_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
      
    <2>2. (currentTerm = currentTerm)'
      BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv4_c57a_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>3. (state = state)'
      BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv4_c57a_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>4. (log = log)'
      BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv4_c57a_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>5. (votedFor = votedFor)'
      BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv4_c57a_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>6. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Inv4_c57a_R6_2_I1
  \* (Inv4_c57a_R6_2_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv4_c57a_R6_2_I1 /\ BecomeLeaderAction => Inv4_c57a_R6_2_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv4_c57a_R6_2_I1,
                        TRUE,
                        NEW i \in Server,
                        BecomeLeader(i)
                 PROVE  Inv4_c57a_R6_2_I1'
      BY DEF BecomeLeaderAction
    <2>1. H_LogEntryInTermImpliesSafeAtTerm'
      <3> SUFFICES ASSUME NEW s \in Server',
                          NEW i_1 \in (DOMAIN log[s])'
                   PROVE  (  \E Q \in Quorum : 
                           \E u \in Server : 
                               /\ currentTerm[u] >= log[s][i_1]
                               /\ (currentTerm[u] = log[s][i_1]) => (state[u] = Leader /\ votesGranted[u] = Q)
                               /\ \A n \in Q : 
                                   /\ currentTerm[n] >= log[s][i_1]
                                   /\ currentTerm[n] = log[s][i_1] => (votedFor[n] = u))'
        BY DEF H_LogEntryInTermImpliesSafeAtTerm
      <3> QED
        BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv4_c57a_R6_2_I1
      
    <2>2. (currentTerm = currentTerm)'
      BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv4_c57a_R6_2_I1
    <2>3. (state = state)'
      BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv4_c57a_R6_2_I1
    <2>4. (log = log)'
      BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv4_c57a_R6_2_I1
    <2>5. (votedFor = votedFor)'
      BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv4_c57a_R6_2_I1
    <2>6. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Inv4_c57a_R6_2_I1
  \* (Inv4_c57a_R6_2_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv166_e30e_R11_0_I1 /\ Inv40_6261_R15_1_I1 /\ Inv82_3acc_R6_1_I1 /\ Inv0_2c32_R8_1_I1 /\ Inv4_c57a_R6_2_I1 /\ ClientRequestAction => Inv4_c57a_R6_2_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv166_e30e_R11_0_I1,
                        Inv40_6261_R15_1_I1,
                        Inv82_3acc_R6_1_I1,
                        Inv0_2c32_R8_1_I1,
                        Inv4_c57a_R6_2_I1,
                        TRUE,
                        NEW i \in Server,
                        ClientRequest(i)
                 PROVE  Inv4_c57a_R6_2_I1'
      BY DEF ClientRequestAction
    <2>1. H_LogEntryInTermImpliesSafeAtTerm'
      <3> SUFFICES ASSUME NEW s \in Server',
                          NEW i_1 \in (DOMAIN log[s])'
                   PROVE  (  \E Q \in Quorum : 
                           \E u \in Server : 
                               /\ currentTerm[u] >= log[s][i_1]
                               /\ (currentTerm[u] = log[s][i_1]) => (state[u] = Leader /\ votesGranted[u] = Q)
                               /\ \A n \in Q : 
                                   /\ currentTerm[n] >= log[s][i_1]
                                   /\ currentTerm[n] = log[s][i_1] => (votedFor[n] = u))'
        BY DEF H_LogEntryInTermImpliesSafeAtTerm
      <3> QED
        BY SMTT(300), THREE_SERVERS_Assumption DEF TypeOK,Inv166_e30e_R11_0_I1,Inv40_6261_R15_1_I1,Inv82_3acc_R6_1_I1,Inv0_2c32_R8_1_I1,ClientRequestAction,ClientRequest,Inv4_c57a_R6_2_I1
      
    <2>2. (currentTerm = currentTerm)'
      BY DEF TypeOK,Inv166_e30e_R11_0_I1,Inv40_6261_R15_1_I1,Inv82_3acc_R6_1_I1,Inv0_2c32_R8_1_I1,ClientRequestAction,ClientRequest,Inv4_c57a_R6_2_I1
    <2>3. (state = state)'
      BY DEF TypeOK,Inv166_e30e_R11_0_I1,Inv40_6261_R15_1_I1,Inv82_3acc_R6_1_I1,Inv0_2c32_R8_1_I1,ClientRequestAction,ClientRequest,Inv4_c57a_R6_2_I1
    <2>4. (log = log)'
      BY DEF TypeOK,Inv166_e30e_R11_0_I1,Inv40_6261_R15_1_I1,Inv82_3acc_R6_1_I1,Inv0_2c32_R8_1_I1,ClientRequestAction,ClientRequest,Inv4_c57a_R6_2_I1
    <2>5. (votedFor = votedFor)'
      BY DEF TypeOK,Inv166_e30e_R11_0_I1,Inv40_6261_R15_1_I1,Inv82_3acc_R6_1_I1,Inv0_2c32_R8_1_I1,ClientRequestAction,ClientRequest,Inv4_c57a_R6_2_I1
    <2>6. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Inv4_c57a_R6_2_I1
  \* (Inv4_c57a_R6_2_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv4_c57a_R6_2_I1 /\ AppendEntriesAction => Inv4_c57a_R6_2_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv4_c57a_R6_2_I1,
                        AppendEntriesAction
                 PROVE  Inv4_c57a_R6_2_I1'
      OBVIOUS
    <2>1. H_LogEntryInTermImpliesSafeAtTerm'
      <3> SUFFICES ASSUME NEW i \in Server, NEW j \in Server,
                          AppendEntries(i, j),
                          NEW s \in Server',
                          NEW i_1 \in (DOMAIN log[s])'
                   PROVE  (  \E Q \in Quorum : 
                           \E u \in Server : 
                               /\ currentTerm[u] >= log[s][i_1]
                               /\ (currentTerm[u] = log[s][i_1]) => (state[u] = Leader /\ votesGranted[u] = Q)
                               /\ \A n \in Q : 
                                   /\ currentTerm[n] >= log[s][i_1]
                                   /\ currentTerm[n] = log[s][i_1] => (votedFor[n] = u))'
        BY DEF AppendEntriesAction, H_LogEntryInTermImpliesSafeAtTerm
      <3> QED
        BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv4_c57a_R6_2_I1
      
    <2>2. (currentTerm = currentTerm)'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv4_c57a_R6_2_I1
    <2>3. (state = state)'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv4_c57a_R6_2_I1
    <2>4. (log = log)'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv4_c57a_R6_2_I1
    <2>5. (votedFor = votedFor)'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv4_c57a_R6_2_I1
    <2>6. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Inv4_c57a_R6_2_I1
  \* (Inv4_c57a_R6_2_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv4_c57a_R6_2_I1 /\ HandleRequestVoteRequestAction => Inv4_c57a_R6_2_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv4_c57a_R6_2_I1,
                        NEW m \in requestVoteRequestMsgs,
                        HandleRequestVoteRequest(m)
                 PROVE  Inv4_c57a_R6_2_I1'
      BY DEF HandleRequestVoteRequestAction
    <2>1. H_LogEntryInTermImpliesSafeAtTerm'
      <3> SUFFICES ASSUME NEW s \in Server',
                          NEW i \in (DOMAIN log[s])'
                   PROVE  (\E Q \in Quorum : 
                           \E u \in Server : 
                               /\ currentTerm[u] >= log[s][i]
                               /\ (currentTerm[u] = log[s][i]) => (state[u] = Leader /\ votesGranted[u] = Q)
                               /\ \A n \in Q : 
                                   /\ currentTerm[n] >= log[s][i]
                                   /\ currentTerm[n] = log[s][i] => (votedFor[n] = u))'
        BY DEF H_LogEntryInTermImpliesSafeAtTerm
      <3> QED
        BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv4_c57a_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
      
    <2>2. (currentTerm = currentTerm)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv4_c57a_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>3. (state = state)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv4_c57a_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>4. (log = log)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv4_c57a_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>5. (votedFor = votedFor)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv4_c57a_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>6. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Inv4_c57a_R6_2_I1
  \* (Inv4_c57a_R6_2_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv1281_1f30_R6_2_I1 /\ Inv14_f533_R11_2_I0 /\ Inv363_d176_R15_2_I1 /\ Inv4_c57a_R6_2_I1 /\ HandleRequestVoteResponseAction => Inv4_c57a_R6_2_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv1281_1f30_R6_2_I1,
                        Inv14_f533_R11_2_I0,
                        Inv363_d176_R15_2_I1,
                        Inv4_c57a_R6_2_I1,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m)
                 PROVE  Inv4_c57a_R6_2_I1'
      BY DEF HandleRequestVoteResponseAction
    <2>1. H_LogEntryInTermImpliesSafeAtTerm'
      <3> SUFFICES ASSUME NEW s \in Server',
                          NEW i \in (DOMAIN log[s])'
                   PROVE  (\E Q \in Quorum : 
                           \E u \in Server : 
                               /\ currentTerm[u] >= log[s][i]
                               /\ (currentTerm[u] = log[s][i]) => (state[u] = Leader /\ votesGranted[u] = Q)
                               /\ \A n \in Q : 
                                   /\ currentTerm[n] >= log[s][i]
                                   /\ currentTerm[n] = log[s][i] => (votedFor[n] = u))'
        BY DEF H_LogEntryInTermImpliesSafeAtTerm
      <3> QED
        BY SMTT(300), TWO_SERVERS_Assumption DEF TypeOK,Inv1281_1f30_R6_2_I1,Inv14_f533_R11_2_I0,Inv363_d176_R15_2_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv4_c57a_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
      
    <2>2. (currentTerm = currentTerm)'
      BY DEF TypeOK,Inv1281_1f30_R6_2_I1,Inv14_f533_R11_2_I0,Inv363_d176_R15_2_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv4_c57a_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>3. (state = state)'
      BY DEF TypeOK,Inv1281_1f30_R6_2_I1,Inv14_f533_R11_2_I0,Inv363_d176_R15_2_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv4_c57a_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>4. (log = log)'
      BY DEF TypeOK,Inv1281_1f30_R6_2_I1,Inv14_f533_R11_2_I0,Inv363_d176_R15_2_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv4_c57a_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>5. (votedFor = votedFor)'
      BY DEF TypeOK,Inv1281_1f30_R6_2_I1,Inv14_f533_R11_2_I0,Inv363_d176_R15_2_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv4_c57a_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>6. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Inv4_c57a_R6_2_I1
  \* (Inv4_c57a_R6_2_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv8_2014_R15_0_I0 /\ Inv0_33b0_R0_0_I0 /\ Inv4_c57a_R6_2_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv4_c57a_R6_2_I1' BY DEF TypeOK,Inv8_2014_R15_0_I0,Inv0_33b0_R0_0_I0,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv4_c57a_R6_2_I1
  \* (Inv4_c57a_R6_2_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv4_c57a_R6_2_I1 /\ HandleAppendEntriesResponseAction => Inv4_c57a_R6_2_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv4_c57a_R6_2_I1,
                        NEW m \in appendEntriesResponseMsgs,
                        HandleAppendEntriesResponse(m)
                 PROVE  Inv4_c57a_R6_2_I1'
      BY DEF HandleAppendEntriesResponseAction
    <2>1. H_LogEntryInTermImpliesSafeAtTerm'
      <3> SUFFICES ASSUME NEW s \in Server',
                          NEW i \in (DOMAIN log[s])'
                   PROVE  (\E Q \in Quorum : 
                           \E u \in Server : 
                               /\ currentTerm[u] >= log[s][i]
                               /\ (currentTerm[u] = log[s][i]) => (state[u] = Leader /\ votesGranted[u] = Q)
                               /\ \A n \in Q : 
                                   /\ currentTerm[n] >= log[s][i]
                                   /\ currentTerm[n] = log[s][i] => (votedFor[n] = u))'
        BY DEF H_LogEntryInTermImpliesSafeAtTerm
      <3> QED
        BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv4_c57a_R6_2_I1
      
    <2>2. (currentTerm = currentTerm)'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv4_c57a_R6_2_I1
    <2>3. (state = state)'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv4_c57a_R6_2_I1
    <2>4. (log = log)'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv4_c57a_R6_2_I1
    <2>5. (votedFor = votedFor)'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv4_c57a_R6_2_I1
    <2>6. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Inv4_c57a_R6_2_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv8_2014_R15_0_I0
THEOREM L_23 == TypeOK /\ Inv4_c57a_R6_2_I1 /\ Inv8_2014_R15_0_I0 /\ Next => Inv8_2014_R15_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv8_2014_R15_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv8_2014_R15_0_I0 /\ RequestVoteAction => Inv8_2014_R15_0_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv8_2014_R15_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv8_2014_R15_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv8_2014_R15_0_I0 /\ UpdateTermAction => Inv8_2014_R15_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv8_2014_R15_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv8_2014_R15_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv8_2014_R15_0_I0 /\ BecomeLeaderAction => Inv8_2014_R15_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv8_2014_R15_0_I0
  \* (Inv8_2014_R15_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv8_2014_R15_0_I0 /\ ClientRequestAction => Inv8_2014_R15_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv8_2014_R15_0_I0
  \* (Inv8_2014_R15_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv4_c57a_R6_2_I1 /\ Inv8_2014_R15_0_I0 /\ AppendEntriesAction => Inv8_2014_R15_0_I0' BY DEF TypeOK,Inv4_c57a_R6_2_I1,AppendEntriesAction,AppendEntries,Inv8_2014_R15_0_I0
  \* (Inv8_2014_R15_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv8_2014_R15_0_I0 /\ HandleRequestVoteRequestAction => Inv8_2014_R15_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv8_2014_R15_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv8_2014_R15_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv8_2014_R15_0_I0 /\ HandleRequestVoteResponseAction => Inv8_2014_R15_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv8_2014_R15_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv8_2014_R15_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv8_2014_R15_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv8_2014_R15_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv8_2014_R15_0_I0
  \* (Inv8_2014_R15_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv8_2014_R15_0_I0 /\ HandleAppendEntriesResponseAction => Inv8_2014_R15_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv8_2014_R15_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv40_6261_R15_1_I1
THEOREM L_24 == TypeOK /\ Inv40_6261_R15_1_I1 /\ Next => Inv40_6261_R15_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv40_6261_R15_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv40_6261_R15_1_I1 /\ RequestVoteAction => Inv40_6261_R15_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv40_6261_R15_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv40_6261_R15_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv40_6261_R15_1_I1 /\ UpdateTermAction => Inv40_6261_R15_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv40_6261_R15_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv40_6261_R15_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv40_6261_R15_1_I1 /\ BecomeLeaderAction => Inv40_6261_R15_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv40_6261_R15_1_I1
  \* (Inv40_6261_R15_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv40_6261_R15_1_I1 /\ ClientRequestAction => Inv40_6261_R15_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv40_6261_R15_1_I1
  \* (Inv40_6261_R15_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv40_6261_R15_1_I1 /\ AppendEntriesAction => Inv40_6261_R15_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv40_6261_R15_1_I1
  \* (Inv40_6261_R15_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv40_6261_R15_1_I1 /\ HandleRequestVoteRequestAction => Inv40_6261_R15_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv40_6261_R15_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv40_6261_R15_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv40_6261_R15_1_I1 /\ HandleRequestVoteResponseAction => Inv40_6261_R15_1_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv40_6261_R15_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv40_6261_R15_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv40_6261_R15_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv40_6261_R15_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv40_6261_R15_1_I1
  \* (Inv40_6261_R15_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv40_6261_R15_1_I1 /\ HandleAppendEntriesResponseAction => Inv40_6261_R15_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv40_6261_R15_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv82_3acc_R6_1_I1
THEOREM L_25 == TypeOK /\ Inv82_3acc_R6_1_I1 /\ Next => Inv82_3acc_R6_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv82_3acc_R6_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv82_3acc_R6_1_I1 /\ RequestVoteAction => Inv82_3acc_R6_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv82_3acc_R6_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv82_3acc_R6_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv82_3acc_R6_1_I1 /\ UpdateTermAction => Inv82_3acc_R6_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv82_3acc_R6_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv82_3acc_R6_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv82_3acc_R6_1_I1 /\ BecomeLeaderAction => Inv82_3acc_R6_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv82_3acc_R6_1_I1
  \* (Inv82_3acc_R6_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv82_3acc_R6_1_I1 /\ ClientRequestAction => Inv82_3acc_R6_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv82_3acc_R6_1_I1
  \* (Inv82_3acc_R6_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv82_3acc_R6_1_I1 /\ AppendEntriesAction => Inv82_3acc_R6_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv82_3acc_R6_1_I1
  \* (Inv82_3acc_R6_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv82_3acc_R6_1_I1 /\ HandleRequestVoteRequestAction => Inv82_3acc_R6_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv82_3acc_R6_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv82_3acc_R6_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv82_3acc_R6_1_I1 /\ HandleRequestVoteResponseAction => Inv82_3acc_R6_1_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv82_3acc_R6_1_I1,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server'
                 PROVE  ((votesGranted[VARI] \in Quorum) \/ (~((state[VARI] = Leader))))'
      BY DEF HandleRequestVoteResponseAction, Inv82_3acc_R6_1_I1
    <2> QED
      BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv82_3acc_R6_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv82_3acc_R6_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv82_3acc_R6_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv82_3acc_R6_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv82_3acc_R6_1_I1
  \* (Inv82_3acc_R6_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv82_3acc_R6_1_I1 /\ HandleAppendEntriesResponseAction => Inv82_3acc_R6_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv82_3acc_R6_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv363_d176_R15_2_I1
THEOREM L_26 == TypeOK /\ Inv14_f533_R11_2_I0 /\ Inv13_3715_R21_0_I0 /\ Inv14_f533_R11_2_I0 /\ Inv13_3715_R21_0_I0 /\ Inv363_d176_R15_2_I1 /\ Next => Inv363_d176_R15_2_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv363_d176_R15_2_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv14_f533_R11_2_I0 /\ Inv13_3715_R21_0_I0 /\ Inv363_d176_R15_2_I1 /\ RequestVoteAction => Inv363_d176_R15_2_I1' BY DEF TypeOK,Inv14_f533_R11_2_I0,Inv13_3715_R21_0_I0,RequestVoteAction,RequestVote,Inv363_d176_R15_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv363_d176_R15_2_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv14_f533_R11_2_I0 /\ Inv363_d176_R15_2_I1 /\ UpdateTermAction => Inv363_d176_R15_2_I1' BY DEF TypeOK,Inv14_f533_R11_2_I0,UpdateTermAction,UpdateTerm,Inv363_d176_R15_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv363_d176_R15_2_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv363_d176_R15_2_I1 /\ BecomeLeaderAction => Inv363_d176_R15_2_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv363_d176_R15_2_I1
  \* (Inv363_d176_R15_2_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv363_d176_R15_2_I1 /\ ClientRequestAction => Inv363_d176_R15_2_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv363_d176_R15_2_I1
  \* (Inv363_d176_R15_2_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv363_d176_R15_2_I1 /\ AppendEntriesAction => Inv363_d176_R15_2_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv363_d176_R15_2_I1
  \* (Inv363_d176_R15_2_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv13_3715_R21_0_I0 /\ Inv363_d176_R15_2_I1 /\ HandleRequestVoteRequestAction => Inv363_d176_R15_2_I1' BY DEF TypeOK,Inv13_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv363_d176_R15_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv363_d176_R15_2_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv363_d176_R15_2_I1 /\ HandleRequestVoteResponseAction => Inv363_d176_R15_2_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv363_d176_R15_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv363_d176_R15_2_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv363_d176_R15_2_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv363_d176_R15_2_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv363_d176_R15_2_I1
  \* (Inv363_d176_R15_2_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv363_d176_R15_2_I1 /\ HandleAppendEntriesResponseAction => Inv363_d176_R15_2_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv363_d176_R15_2_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv7_8db7_R7_1_I1
THEOREM L_27 == TypeOK /\ Inv11_afc0_R17_0_I0 /\ Inv7_8db7_R7_1_I1 /\ Next => Inv7_8db7_R7_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv7_8db7_R7_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv7_8db7_R7_1_I1 /\ RequestVoteAction => Inv7_8db7_R7_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv7_8db7_R7_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7_8db7_R7_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv7_8db7_R7_1_I1 /\ UpdateTermAction => Inv7_8db7_R7_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv7_8db7_R7_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7_8db7_R7_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv7_8db7_R7_1_I1 /\ BecomeLeaderAction => Inv7_8db7_R7_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv7_8db7_R7_1_I1
  \* (Inv7_8db7_R7_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv7_8db7_R7_1_I1 /\ ClientRequestAction => Inv7_8db7_R7_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv7_8db7_R7_1_I1
  \* (Inv7_8db7_R7_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv11_afc0_R17_0_I0 /\ Inv7_8db7_R7_1_I1 /\ AppendEntriesAction => Inv7_8db7_R7_1_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv11_afc0_R17_0_I0,
                        Inv7_8db7_R7_1_I1,
                        TRUE,
                        NEW i \in Server, NEW j \in Server,
                        AppendEntries(i, j),
                        NEW VARI \in Server',
                        NEW VARJ \in Server',
                        NEW VARMAEREQ \in appendEntriesRequestMsgs'
                 PROVE  (((currentTerm[VARJ] > currentTerm[VARI])) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] > VARMAEREQ.mterm)))'
      BY DEF AppendEntriesAction, Inv7_8db7_R7_1_I1
    <2> QED
      BY SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq, TWO_SERVERS_Assumption
      DEF Min, TypeOK,Inv11_afc0_R17_0_I0,AppendEntriesAction,AppendEntries,Inv7_8db7_R7_1_I1,AppendEntriesRequestType
  \* (Inv7_8db7_R7_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv7_8db7_R7_1_I1 /\ HandleRequestVoteRequestAction => Inv7_8db7_R7_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7_8db7_R7_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7_8db7_R7_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv7_8db7_R7_1_I1 /\ HandleRequestVoteResponseAction => Inv7_8db7_R7_1_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv7_8db7_R7_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7_8db7_R7_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv7_8db7_R7_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv7_8db7_R7_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv7_8db7_R7_1_I1
  \* (Inv7_8db7_R7_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv7_8db7_R7_1_I1 /\ HandleAppendEntriesResponseAction => Inv7_8db7_R7_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv7_8db7_R7_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv11_afc0_R17_0_I0
THEOREM L_28 == TypeOK /\ Inv21_c904_R28_0_I0 /\ Inv11_afc0_R17_0_I0 /\ Next => Inv11_afc0_R17_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv11_afc0_R17_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv11_afc0_R17_0_I0 /\ RequestVoteAction => Inv11_afc0_R17_0_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv11_afc0_R17_0_I0,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW INDK \in (DOMAIN log[VARI])'
                 PROVE  (log[VARI][INDK] <= currentTerm[VARI])'
      BY DEF Inv11_afc0_R17_0_I0, RequestVoteAction
    <2> QED
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv11_afc0_R17_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv11_afc0_R17_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv11_afc0_R17_0_I0 /\ UpdateTermAction => Inv11_afc0_R17_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv11_afc0_R17_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv11_afc0_R17_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv11_afc0_R17_0_I0 /\ BecomeLeaderAction => Inv11_afc0_R17_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv11_afc0_R17_0_I0
  \* (Inv11_afc0_R17_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv11_afc0_R17_0_I0 /\ ClientRequestAction => Inv11_afc0_R17_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv11_afc0_R17_0_I0
  \* (Inv11_afc0_R17_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv11_afc0_R17_0_I0 /\ AppendEntriesAction => Inv11_afc0_R17_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv11_afc0_R17_0_I0
  \* (Inv11_afc0_R17_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv11_afc0_R17_0_I0 /\ HandleRequestVoteRequestAction => Inv11_afc0_R17_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv11_afc0_R17_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv11_afc0_R17_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv11_afc0_R17_0_I0 /\ HandleRequestVoteResponseAction => Inv11_afc0_R17_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv11_afc0_R17_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv11_afc0_R17_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv21_c904_R28_0_I0 /\ Inv11_afc0_R17_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv11_afc0_R17_0_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv21_c904_R28_0_I0,
                        Inv11_afc0_R17_0_I0,
                        NEW m \in appendEntriesRequestMsgs,
                        AcceptAppendEntriesRequestAppend(m),
                        NEW VARI \in Server',
                        NEW INDK \in (DOMAIN log[VARI])'
                 PROVE  (log[VARI][INDK] <= currentTerm[VARI])'
      BY DEF AcceptAppendEntriesRequestAppendAction, Inv11_afc0_R17_0_I0
    <2> QED
      BY SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq 
      DEF LogOk, CanAppend, TypeOK,Inv21_c904_R28_0_I0,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv11_afc0_R17_0_I0,AppendEntriesRequestType
  \* (Inv11_afc0_R17_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv11_afc0_R17_0_I0 /\ HandleAppendEntriesResponseAction => Inv11_afc0_R17_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv11_afc0_R17_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv21_c904_R28_0_I0
THEOREM L_29 == TypeOK /\ Inv11_afc0_R17_0_I0 /\ Inv21_c904_R28_0_I0 /\ Next => Inv21_c904_R28_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv21_c904_R28_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv21_c904_R28_0_I0 /\ RequestVoteAction => Inv21_c904_R28_0_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv21_c904_R28_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv21_c904_R28_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv21_c904_R28_0_I0 /\ UpdateTermAction => Inv21_c904_R28_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv21_c904_R28_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv21_c904_R28_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv21_c904_R28_0_I0 /\ BecomeLeaderAction => Inv21_c904_R28_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv21_c904_R28_0_I0
  \* (Inv21_c904_R28_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv21_c904_R28_0_I0 /\ ClientRequestAction => Inv21_c904_R28_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv21_c904_R28_0_I0
  \* (Inv21_c904_R28_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv11_afc0_R17_0_I0 /\ Inv21_c904_R28_0_I0 /\ AppendEntriesAction => Inv21_c904_R28_0_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv11_afc0_R17_0_I0,
                        Inv21_c904_R28_0_I0,
                        TRUE,
                        NEW i \in Server, NEW j \in Server,
                        AppendEntries(i, j),
                        NEW VARMAEREQ \in appendEntriesRequestMsgs'
                 PROVE  (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] > VARMAEREQ.mterm))'
      BY DEF AppendEntriesAction, Inv21_c904_R28_0_I0
    <2>1. CASE VARMAEREQ.mentries = <<>>
          BY <2>1, SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq,SMTT(300), TWO_SERVERS_Assumption
          DEF TypeOK,Inv11_afc0_R17_0_I0,AppendEntriesAction,AppendEntries,Inv21_c904_R28_0_I0,AppendEntriesRequestType,AppendEntriesRequestType
    <2>2. CASE VARMAEREQ.mentries # <<>>
\*          BY <2>1, SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq,SMTT(300), TWO_SERVERS_Assumption
\*          DEF TypeOK,Inv11_afc0_R17_0_I0,AppendEntriesAction,AppendEntries,Inv21_c904_R28_0_I0,AppendEntriesRequestType,AppendEntriesRequestType
          <3>0. CASE Len(log[i]) = 0
            BY <3>0, SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq,SMTT(300), TWO_SERVERS_Assumption
            DEF TypeOK,Inv11_afc0_R17_0_I0,AppendEntriesAction,AppendEntries,Inv21_c904_R28_0_I0,AppendEntriesRequestType,AppendEntriesRequestType
          <3>1. VARMAEREQ.mentries[1] = log[i][nextIndex[i][j]]
            BY <2>1, SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq,SMTT(300), TWO_SERVERS_Assumption
            DEF TypeOK,Inv11_afc0_R17_0_I0,AppendEntriesAction,AppendEntries,Inv21_c904_R28_0_I0,AppendEntriesRequestType,AppendEntriesRequestType
           <3>2. QED BY <3>1
    <2> QED
      BY SubSeqProperties,EmptySeq,LenProperties,ElementOfSeq,SMTT(300), TWO_SERVERS_Assumption
      DEF TypeOK,Inv11_afc0_R17_0_I0,AppendEntriesAction,AppendEntries,Inv21_c904_R28_0_I0,AppendEntriesRequestType,AppendEntriesRequestType
  \* (Inv21_c904_R28_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv21_c904_R28_0_I0 /\ HandleRequestVoteRequestAction => Inv21_c904_R28_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv21_c904_R28_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv21_c904_R28_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv21_c904_R28_0_I0 /\ HandleRequestVoteResponseAction => Inv21_c904_R28_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv21_c904_R28_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv21_c904_R28_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv21_c904_R28_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv21_c904_R28_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv21_c904_R28_0_I0
  \* (Inv21_c904_R28_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv21_c904_R28_0_I0 /\ HandleAppendEntriesResponseAction => Inv21_c904_R28_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv21_c904_R28_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv173_650b_R7_1_I1
THEOREM L_30 == TypeOK /\ Inv8_2014_R15_0_I0 /\ Inv8_2014_R15_0_I0 /\ Inv4_c57a_R6_2_I1 /\ Inv8_2014_R15_0_I0 /\ Inv173_650b_R7_1_I1 /\ Next => Inv173_650b_R7_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF H_LogEntryInTermImpliesSafeAtTermAppendEntries
  \* (Inv173_650b_R7_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv8_2014_R15_0_I0 /\ Inv173_650b_R7_1_I1 /\ RequestVoteAction => Inv173_650b_R7_1_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv8_2014_R15_0_I0,
                        Inv173_650b_R7_1_I1,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARREQVRES \in requestVoteResponseMsgs'
                 PROVE  ((H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ currentTerm = currentTerm /\ state = state /\ log = log /\ votedFor = votedFor /\ appendEntriesRequestMsgs = appendEntriesRequestMsgs) \/ (~(currentTerm[VARREQVRES.mdest] >= VARREQVRES.mterm)))'
      BY DEF Inv173_650b_R7_1_I1, RequestVoteAction
    <2> QED
      BY DEF TypeOK,Inv8_2014_R15_0_I0,RequestVoteAction,RequestVote,Inv173_650b_R7_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv173_650b_R7_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv8_2014_R15_0_I0 /\ Inv173_650b_R7_1_I1 /\ UpdateTermAction => Inv173_650b_R7_1_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv8_2014_R15_0_I0,
                        Inv173_650b_R7_1_I1,
                        TRUE,
                        NEW m \in requestVoteRequestMsgs \cup requestVoteResponseMsgs \cup appendEntriesRequestMsgs \cup appendEntriesResponseMsgs,
                        UpdateTerm(m, m.mterm, m.mdest),
                        NEW VARREQVRES \in requestVoteResponseMsgs'
                 PROVE  ((H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ currentTerm = currentTerm /\ state = state /\ log = log /\ votedFor = votedFor /\ appendEntriesRequestMsgs = appendEntriesRequestMsgs) \/ (~(currentTerm[VARREQVRES.mdest] >= VARREQVRES.mterm)))'
      BY DEF Inv173_650b_R7_1_I1, UpdateTermAction
    <2> QED
      BY SMTT(500), FIVE_SERVERS_Assumption 
      DEF TypeOK,Inv8_2014_R15_0_I0,UpdateTermAction,UpdateTerm,Inv173_650b_R7_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv173_650b_R7_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv173_650b_R7_1_I1 /\ BecomeLeaderAction => Inv173_650b_R7_1_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv173_650b_R7_1_I1,
                        TRUE,
                        NEW i \in Server,
                        BecomeLeader(i),
                        NEW VARREQVRES \in requestVoteResponseMsgs'
                 PROVE  ((H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ currentTerm = currentTerm /\ state = state /\ log = log /\ votedFor = votedFor /\ appendEntriesRequestMsgs = appendEntriesRequestMsgs) \/ (~(currentTerm[VARREQVRES.mdest] >= VARREQVRES.mterm)))'
      BY DEF BecomeLeaderAction, Inv173_650b_R7_1_I1
    <2> QED
      BY SMTT(500), FIVE_SERVERS_Assumption DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv173_650b_R7_1_I1, RequestVoteResponseType, AppendEntriesRequestType
  \* (Inv173_650b_R7_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv173_650b_R7_1_I1 /\ ClientRequestAction => Inv173_650b_R7_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv173_650b_R7_1_I1
  \* (Inv173_650b_R7_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv4_c57a_R6_2_I1 /\ Inv173_650b_R7_1_I1 /\ AppendEntriesAction => Inv173_650b_R7_1_I1' BY DEF TypeOK,Inv4_c57a_R6_2_I1,AppendEntriesAction,AppendEntries,Inv173_650b_R7_1_I1
  \* (Inv173_650b_R7_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv8_2014_R15_0_I0 /\ Inv173_650b_R7_1_I1 /\ HandleRequestVoteRequestAction => Inv173_650b_R7_1_I1' BY DEF TypeOK,Inv8_2014_R15_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv173_650b_R7_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv173_650b_R7_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv173_650b_R7_1_I1 /\ HandleRequestVoteResponseAction => Inv173_650b_R7_1_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv173_650b_R7_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv173_650b_R7_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv173_650b_R7_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv173_650b_R7_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv173_650b_R7_1_I1
  \* (Inv173_650b_R7_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv173_650b_R7_1_I1 /\ HandleAppendEntriesResponseAction => Inv173_650b_R7_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv173_650b_R7_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv15_7bad_R0_2_I0
THEOREM L_31 == TypeOK /\ Inv11_d848_R2_1_I0 /\ Inv15_7bad_R0_2_I0 /\ Next => Inv15_7bad_R0_2_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv15_7bad_R0_2_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv15_7bad_R0_2_I0 /\ RequestVoteAction => Inv15_7bad_R0_2_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv15_7bad_R0_2_I0,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (~((state[VARI] = Leader /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) \/ (~((state[VARJ] = Leader))))'
      BY DEF Inv15_7bad_R0_2_I0, RequestVoteAction
    <2> QED
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv15_7bad_R0_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv15_7bad_R0_2_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv15_7bad_R0_2_I0 /\ UpdateTermAction => Inv15_7bad_R0_2_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv15_7bad_R0_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv15_7bad_R0_2_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv11_d848_R2_1_I0 /\ Inv15_7bad_R0_2_I0 /\ BecomeLeaderAction => Inv15_7bad_R0_2_I0' BY DEF TypeOK,Inv11_d848_R2_1_I0,BecomeLeaderAction,BecomeLeader,Inv15_7bad_R0_2_I0
  \* (Inv15_7bad_R0_2_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv15_7bad_R0_2_I0 /\ ClientRequestAction => Inv15_7bad_R0_2_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv15_7bad_R0_2_I0
  \* (Inv15_7bad_R0_2_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv15_7bad_R0_2_I0 /\ AppendEntriesAction => Inv15_7bad_R0_2_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv15_7bad_R0_2_I0
  \* (Inv15_7bad_R0_2_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv15_7bad_R0_2_I0 /\ HandleRequestVoteRequestAction => Inv15_7bad_R0_2_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv15_7bad_R0_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv15_7bad_R0_2_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv15_7bad_R0_2_I0 /\ HandleRequestVoteResponseAction => Inv15_7bad_R0_2_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv15_7bad_R0_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv15_7bad_R0_2_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv15_7bad_R0_2_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv15_7bad_R0_2_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv15_7bad_R0_2_I0
  \* (Inv15_7bad_R0_2_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv15_7bad_R0_2_I0 /\ HandleAppendEntriesResponseAction => Inv15_7bad_R0_2_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv15_7bad_R0_2_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0,A1,A2,A3,A4,A5,A6,A7
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal
    <1>2. Init => Inv0_33b0_R0_0_I0 BY DEF Init, Inv0_33b0_R0_0_I0, IndGlobal
    <1>3. Init => Inv12_e9c6_R1_1_I0 BY DEF Init, Inv12_e9c6_R1_1_I0, IndGlobal
    <1>4. Init => Inv24_ed8d_R0_1_I0 BY DEF Init, Inv24_ed8d_R0_1_I0, IndGlobal
    <1>5. Init => Inv11_d848_R2_1_I0 BY DEF Init, Inv11_d848_R2_1_I0, IndGlobal
    <1>6. Init => Inv8_8e53_R5_0_I0 BY DEF Init, Inv8_8e53_R5_0_I0, IndGlobal
    <1>7. Init => Inv9_42ac_R5_1_I2 BY DEF Init, Inv9_42ac_R5_1_I2, IndGlobal
    <1>8. Init => Inv166_e30e_R11_0_I1 BY DEF Init, Inv166_e30e_R11_0_I1, IndGlobal
    <1>9. Init => Inv13_3715_R21_0_I0 BY DEF Init, Inv13_3715_R21_0_I0, IndGlobal
    <1>10. Init => Inv14_f533_R11_2_I0 BY DEF Init, Inv14_f533_R11_2_I0, IndGlobal
    <1>11. Init => Inv0_2c32_R8_1_I1 BY DEF Init, Inv0_2c32_R8_1_I1, IndGlobal
    <1>12. Init => Inv10_82b3_R11_1_I0 BY DEF Init, Inv10_82b3_R11_1_I0, IndGlobal
    <1>13. Init => Inv127_0bd2_R5_1_I2 BY DEF Init, Inv127_0bd2_R5_1_I2, IndGlobal
    <1>14. Init => Inv61_fe26_R9_0_I1 BY DEF Init, Inv61_fe26_R9_0_I1, IndGlobal
    <1>15. Init => Inv2513_1e2e_R6_3_I1 BY DEF Init, Inv2513_1e2e_R6_3_I1, IndGlobal
    <1>16. Init => Inv12_9e78_R16_0_I0 BY DEF Init, Inv12_9e78_R16_0_I0, IndGlobal
    <1>17. Init => Inv9072_27f5_R5_1_I2 BY DEF Init, Inv9072_27f5_R5_1_I2, IndGlobal
    <1>18. Init => Inv33_5a2e_R2_2_I0 BY DEF Init, Inv33_5a2e_R2_2_I0, IndGlobal
    <1>19. Init => Inv15967_602c_R4_1_I2 BY DEF Init, Inv15967_602c_R4_1_I2, IndGlobal
    <1>20. Init => Inv789_4aa6_R6_2_I1 BY DEF Init, Inv789_4aa6_R6_2_I1, IndGlobal
    <1>21. Init => Inv1281_1f30_R6_2_I1 BY DEF Init, Inv1281_1f30_R6_2_I1, IndGlobal
    <1>22. Init => Inv4_c57a_R6_2_I1 BY DEF Init, Inv4_c57a_R6_2_I1, IndGlobal
    <1>23. Init => Inv8_2014_R15_0_I0 BY DEF Init, Inv8_2014_R15_0_I0, IndGlobal
    <1>24. Init => Inv40_6261_R15_1_I1 BY DEF Init, Inv40_6261_R15_1_I1, IndGlobal
    <1>25. Init => Inv82_3acc_R6_1_I1 BY DEF Init, Inv82_3acc_R6_1_I1, IndGlobal
    <1>26. Init => Inv363_d176_R15_2_I1 BY DEF Init, Inv363_d176_R15_2_I1, IndGlobal
    <1>27. Init => Inv7_8db7_R7_1_I1 BY DEF Init, Inv7_8db7_R7_1_I1, IndGlobal
    <1>28. Init => Inv11_afc0_R17_0_I0 BY DEF Init, Inv11_afc0_R17_0_I0, IndGlobal
    <1>29. Init => Inv21_c904_R28_0_I0 BY DEF Init, Inv21_c904_R28_0_I0, IndGlobal
    <1>30. Init => Inv173_650b_R7_1_I1 BY DEF Init, Inv173_650b_R7_1_I1, IndGlobal
    <1>31. Init => Inv15_7bad_R0_2_I0 BY DEF Init, Inv15_7bad_R0_2_I0, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14,<1>15,<1>16,<1>17,<1>18,<1>19,<1>20,<1>21,<1>22,<1>23,<1>24,<1>25,<1>26,<1>27,<1>28,<1>29,<1>30,<1>31 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13,L_14,L_15,L_16,L_17,L_18,L_19,L_20,L_21,L_22,L_23,L_24,L_25,L_26,L_27,L_28,L_29,L_30,L_31 DEF Next, IndGlobal

====
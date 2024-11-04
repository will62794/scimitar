--------------------------------- MODULE AsyncRaft_IndProofs_PrimaryHasEntriesItCreated_1 ---------------------------------
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
\* seed: 1
\* num proof graph nodes: 36
\* num proof obligations: 324
Safety == H_PrimaryHasEntriesItCreated
Inv0_33b0_R0_0_I0 == \A VARI \in Server : \A VARMAEREQ \in appendEntriesRequestMsgs : \A VARLOGINDI \in LogIndices : ((VARLOGINDI \in DOMAIN log[VARI] /\ log[VARI][VARLOGINDI] = currentTerm[VARI]) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI] /\ state[VARI] = Leader)) \/ (~(VARLOGINDI = VARMAEREQ.mprevLogIndex + 1)))
Inv17_ed8d_R0_1_I0 == \A VARI \in Server : \A VARJ \in Server : (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(votesGranted[VARI] \in Quorum)) \/ (~(\E INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] = currentTerm[VARI])))
Inv7_7bad_R0_2_I0 == \A VARI \in Server : \A VARJ \in Server : (~((state[VARI] = Leader /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) \/ (~((state[VARJ] = Leader))))
Inv21336_7e0d_R1_1_I2 == \A VARI \in Server : \A VARMAEREQ \in appendEntriesRequestMsgs : ~((state[VARI] = Candidate)) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI]) \/ (~(votesGranted[VARI] \in Quorum)))
Inv15883_404d_R2_1_I2 == \A VARI \in Server : \A VARJ \in Server : ~((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) \/ (~((state[VARJ] = Leader))) \/ (~(votesGranted[VARI] \in Quorum))
Inv28_5a2e_R2_2_I0 == \A VARI \in Server : \A VARJ \in Server : (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(\E INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] = currentTerm[VARI])) \/ (~(GrantedVoteSet(VARI) \in Quorum /\ votesGranted = votesGranted /\ requestVoteResponseMsgs = requestVoteResponseMsgs)))
Inv22504_7f3f_R4_1_I2 == \A VARI \in Server : \A VARMAEREQ \in appendEntriesRequestMsgs : ~((state[VARI] = Candidate)) \/ (~(GrantedVoteSet(VARI) \in Quorum /\ votesGranted = votesGranted /\ requestVoteResponseMsgs = requestVoteResponseMsgs) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI])))
Inv4_8e53_R5_0_I0 == (\A s,t \in Server : ( /\ s # t /\ state[s] \in {Leader,Candidate} /\ state[t] \in {Leader,Candidate} /\ currentTerm[s] = currentTerm[t]) => votesGranted[s] \cap votesGranted[t] = {})
Inv10_928b_R5_1_I1 == \A VARI \in Server : (VARI \in votesGranted[VARI]) \/ ((votesGranted[VARI] = {}))
Inv42_3acc_R5_1_I1 == \A VARI \in Server : (votesGranted[VARI] \in Quorum) \/ (~((state[VARI] = Leader)))
Inv6_42ac_R5_1_I1 == (\A s,t \in Server : \A m \in requestVoteResponseMsgs :( /\ state[s] \in {Candidate,Leader} /\ t \in votesGranted[s]) => ~(/\ m.mterm = currentTerm[s] /\ m.msource = t /\ m.mdest # s /\ m.mvoteGranted))
Inv109_4308_R6_1_I1 == \A VARI \in Server : \A VARJ \in Server : ((state[VARJ] = Leader)) \/ ((\A INDK \in DOMAIN log[VARI] : log[VARI][INDK] <= currentTerm[VARI]))
Inv672_4aa6_R6_2_I1 == \A VARI \in Server : ((state[VARI] = Follower)) \/ ((votedFor[VARI] # Nil /\ VARI \in votesGranted[votedFor[VARI]]))
Inv4_c57a_R6_2_I1 == (H_LogEntryInTermImpliesSafeAtTerm /\ currentTerm = currentTerm /\ state = state /\ log = log /\ votedFor = votedFor)
Inv1082_1f30_R6_2_I1 == \A VARJ \in Server : ((state[VARJ] = Follower)) \/ ((votedFor[VARJ] = VARJ))
Inv70_1e2e_R6_3_I1 == \A VARREQVRES \in requestVoteResponseMsgs : (currentTerm[VARREQVRES.mdest] >= VARREQVRES.mterm) \/ (~(VARREQVRES.mvoteGranted))
Inv7027_6cb8_R7_1_I2 == \A VARI \in Server : \A VARJ \in Server : \A VARMAEREQ \in appendEntriesRequestMsgs : \A VARLOGINDI \in LogIndices : (VARJ \in votesGranted[VARJ]) \/ ((VARLOGINDI = VARMAEREQ.mprevLogIndex + 1)) \/ (~(VARI \in GrantedVoteSet(VARJ) /\ votesGranted = votesGranted /\ requestVoteResponseMsgs = requestVoteResponseMsgs))
Inv40_2a9c_R7_1_I2 == \A VARI \in Server : \A VARJ \in Server : ((state[VARI] \in {Leader,Candidate} /\ VARI # VARJ)) \/ ((H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ currentTerm = currentTerm /\ state = state /\ log = log /\ votedFor = votedFor /\ appendEntriesRequestMsgs = appendEntriesRequestMsgs))
Inv0_2c32_R8_1_I1 == \A VARI \in Server : \A VARJ \in Server : ((currentTerm[VARI] <= currentTerm[VARJ])) \/ (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])))
Inv877_09bb_R9_0_I1 == \A VARI \in Server : \A VARREQVRES \in requestVoteResponseMsgs : ~(VARREQVRES.mdest = VARI) \/ (~(votesGranted[VARI] = {}))
Inv0_e30e_R11_0_I1 == \A VARI \in Server : ((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI )) \/ (((state[VARI] = Follower)))
Inv9_f533_R11_1_I0 == \A VARREQVRES \in requestVoteResponseMsgs : (currentTerm[VARREQVRES.msource] >= VARREQVRES.mterm)
Inv13_c904_R12_0_I0 == \A VARMAEREQ \in appendEntriesRequestMsgs : ~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] > VARMAEREQ.mterm)
Inv8_2014_R14_0_I1 == (H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ currentTerm = currentTerm /\ state = state /\ log = log /\ votedFor = votedFor /\ appendEntriesRequestMsgs = appendEntriesRequestMsgs)
Inv8_441b_R14_1_I1 == (H_QuorumsSafeAtTerms /\ currentTerm = currentTerm /\ state = state /\ votedFor = votedFor)
Inv8407_edca_R14_2_I2 == \A VARI \in Server : \A VARJ \in Server : \A VARREQVRES \in requestVoteResponseMsgs : (votedFor[VARREQVRES.msource] = VARREQVRES.mdest) \/ (~((currentTerm[VARI] >= currentTerm[VARJ])) \/ (~(VARREQVRES.mterm = currentTerm[VARI] /\ VARREQVRES.msource = VARJ /\ VARREQVRES.mdest # VARI /\ VARREQVRES.mvoteGranted)))
Inv5_9e78_R16_0_I0 == \A VARREQVM \in requestVoteRequestMsgs : (currentTerm[VARREQVM.msource] >= VARREQVM.mterm)
Inv480_fe26_R17_0_I1 == \A VARI \in Server : \A VARREQVM \in requestVoteRequestMsgs : ~(VARREQVM.msource = VARI) \/ (~(votesGranted[VARI] = {}))
Inv1152_5d57_R18_0_I1 == \A VARI \in Server : \A VARJ \in Server : (\A INDK \in DOMAIN log[VARI] : log[VARI][INDK] <= currentTerm[VARI]) \/ ((votedFor[VARI] = VARJ))
Inv10_3715_R21_0_I0 == (\A m \in requestVoteResponseMsgs : m.mtype = RequestVoteResponse =>  /\ (m.mvoteGranted /\ (currentTerm[m.msource] = m.mterm)) => votedFor[m.msource] = m.mdest)
Inv21_a5e5_R23_0_I0 == \A VARI \in Server : ~(\E INDK \in DOMAIN log[VARI] : log[VARI][INDK] > currentTerm[VARI])
Inv18_0a54_R24_0_I0 == \A VARI \in Server : ~((commitIndex[VARI] > 0))
Inv12_afc0_R24_0_I0 == \A VARI \in Server : (\A INDK \in DOMAIN log[VARI] : log[VARI][INDK] <= currentTerm[VARI])
Inv6346_3776_R25_0_I2 == \A VARI \in Server : \A VARJ \in Server : ((state[VARI] = Follower /\ VARI # VARJ)) \/ ((VARI \in votesGranted[VARI])) \/ ((votesGranted[VARJ] = {}))
Inv2_12a2_R34_1_I1 == \A VARI \in Server : ((state[VARI] = Follower)) \/ (~(votesGranted[VARI] = {}))
Inv9_82b3_R10_1_I0 == (\A mi,mj \in requestVoteResponseMsgs : (/\ mi.mterm = mj.mterm /\ mi.msource = mj.msource /\ mi.mvoteGranted /\ mj.mvoteGranted) => mi.mdest = mj.mdest)

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv0_33b0_R0_0_I0
  /\ Inv21336_7e0d_R1_1_I2
  /\ Inv17_ed8d_R0_1_I0
  /\ Inv15883_404d_R2_1_I2
  /\ Inv4_8e53_R5_0_I0
  /\ Inv6_42ac_R5_1_I1
  /\ Inv0_e30e_R11_0_I1
  /\ Inv10_3715_R21_0_I0
  /\ Inv9_f533_R11_1_I0
  /\ Inv0_2c32_R8_1_I1
  /\ Inv10_928b_R5_1_I1
  /\ Inv877_09bb_R9_0_I1
  /\ Inv480_fe26_R17_0_I1
  /\ Inv42_3acc_R5_1_I1
  /\ Inv28_5a2e_R2_2_I0
  /\ Inv22504_7f3f_R4_1_I2
  /\ Inv7027_6cb8_R7_1_I2
  /\ Inv1082_1f30_R6_2_I1
  /\ Inv40_2a9c_R7_1_I2
  /\ Inv1152_5d57_R18_0_I1
  /\ Inv13_c904_R12_0_I0
  /\ Inv21_a5e5_R23_0_I0
  /\ Inv8_441b_R14_1_I1
  /\ Inv6346_3776_R25_0_I2
  /\ Inv2_12a2_R34_1_I1
  /\ Inv70_1e2e_R6_3_I1
  /\ Inv5_9e78_R16_0_I0
  /\ Inv109_4308_R6_1_I1
  /\ Inv672_4aa6_R6_2_I1
  /\ Inv4_c57a_R6_2_I1
  /\ Inv8_2014_R14_0_I1
  /\ Inv18_0a54_R24_0_I0
  /\ Inv12_afc0_R24_0_I0
  /\ Inv8407_edca_R14_2_I2
  /\ Inv7_7bad_R0_2_I0
  /\ Inv9_82b3_R10_1_I0


\* mean in-degree: 2.0833333333333335
\* median in-degree: 2
\* max in-degree: 10
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
  <1>1. TypeOK /\ TypeOK /\ RequestVoteAction => TypeOK' BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
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
THEOREM L_1 == TypeOK /\ Inv17_ed8d_R0_1_I0 /\ Inv7_7bad_R0_2_I0 /\ Inv0_33b0_R0_0_I0 /\ Safety /\ Next => Safety'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Safety,RequestVoteAction)
  <1>1. TypeOK /\ Safety /\ RequestVoteAction => Safety' BY DEF TypeOK,RequestVoteAction,RequestVote,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,UpdateTermAction)
  <1>2. TypeOK /\ Safety /\ UpdateTermAction => Safety' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv17_ed8d_R0_1_I0 /\ Safety /\ BecomeLeaderAction => Safety' BY DEF TypeOK,Inv17_ed8d_R0_1_I0,BecomeLeaderAction,BecomeLeader,Safety,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,ClientRequestAction)
  <1>4. TypeOK /\ Inv7_7bad_R0_2_I0 /\ Safety /\ ClientRequestAction => Safety' BY DEF TypeOK,Inv7_7bad_R0_2_I0,ClientRequestAction,ClientRequest,Safety,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,AppendEntriesAction)
  <1>5. TypeOK /\ Safety /\ AppendEntriesAction => Safety' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Safety,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Safety /\ HandleRequestVoteRequestAction => Safety' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Safety,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Safety /\ HandleRequestVoteResponseAction => Safety' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Safety,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv0_33b0_R0_0_I0 /\ Safety /\ AcceptAppendEntriesRequestAppendAction => Safety' BY DEF TypeOK,Inv0_33b0_R0_0_I0,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Safety,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
  \* (Safety,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Safety /\ HandleAppendEntriesResponseAction => Safety' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Safety,H_OnePrimaryPerTerm,H_PrimaryHasEntriesItCreated
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv0_33b0_R0_0_I0
THEOREM L_2 == TypeOK /\ Inv21336_7e0d_R1_1_I2 /\ Safety /\ Inv0_33b0_R0_0_I0 /\ Next => Inv0_33b0_R0_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv0_33b0_R0_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv0_33b0_R0_0_I0 /\ RequestVoteAction => Inv0_33b0_R0_0_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv0_33b0_R0_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv0_33b0_R0_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv0_33b0_R0_0_I0 /\ UpdateTermAction => Inv0_33b0_R0_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv0_33b0_R0_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv0_33b0_R0_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv21336_7e0d_R1_1_I2 /\ Inv0_33b0_R0_0_I0 /\ BecomeLeaderAction => Inv0_33b0_R0_0_I0' BY DEF TypeOK,Inv21336_7e0d_R1_1_I2,BecomeLeaderAction,BecomeLeader,Inv0_33b0_R0_0_I0
  \* (Inv0_33b0_R0_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv0_33b0_R0_0_I0 /\ ClientRequestAction => Inv0_33b0_R0_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv0_33b0_R0_0_I0
  \* (Inv0_33b0_R0_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Safety /\ Inv0_33b0_R0_0_I0 /\ AppendEntriesAction => Inv0_33b0_R0_0_I0' BY DEF TypeOK,Safety,AppendEntriesAction,AppendEntries,Inv0_33b0_R0_0_I0
  \* (Inv0_33b0_R0_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv0_33b0_R0_0_I0 /\ HandleRequestVoteRequestAction => Inv0_33b0_R0_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv0_33b0_R0_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_33b0_R0_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv0_33b0_R0_0_I0 /\ HandleRequestVoteResponseAction => Inv0_33b0_R0_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv0_33b0_R0_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_33b0_R0_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv0_33b0_R0_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv0_33b0_R0_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv0_33b0_R0_0_I0
  \* (Inv0_33b0_R0_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv0_33b0_R0_0_I0 /\ HandleAppendEntriesResponseAction => Inv0_33b0_R0_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv0_33b0_R0_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv21336_7e0d_R1_1_I2
THEOREM L_3 == TypeOK /\ Inv17_ed8d_R0_1_I0 /\ Inv22504_7f3f_R4_1_I2 /\ Inv21336_7e0d_R1_1_I2 /\ Next => Inv21336_7e0d_R1_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv21336_7e0d_R1_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv21336_7e0d_R1_1_I2 /\ RequestVoteAction => Inv21336_7e0d_R1_1_I2' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv21336_7e0d_R1_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv21336_7e0d_R1_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv21336_7e0d_R1_1_I2 /\ UpdateTermAction => Inv21336_7e0d_R1_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv21336_7e0d_R1_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv21336_7e0d_R1_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv21336_7e0d_R1_1_I2 /\ BecomeLeaderAction => Inv21336_7e0d_R1_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv21336_7e0d_R1_1_I2
  \* (Inv21336_7e0d_R1_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv21336_7e0d_R1_1_I2 /\ ClientRequestAction => Inv21336_7e0d_R1_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv21336_7e0d_R1_1_I2
  \* (Inv21336_7e0d_R1_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv17_ed8d_R0_1_I0 /\ Inv21336_7e0d_R1_1_I2 /\ AppendEntriesAction => Inv21336_7e0d_R1_1_I2' BY DEF TypeOK,Inv17_ed8d_R0_1_I0,AppendEntriesAction,AppendEntries,Inv21336_7e0d_R1_1_I2
  \* (Inv21336_7e0d_R1_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv21336_7e0d_R1_1_I2 /\ HandleRequestVoteRequestAction => Inv21336_7e0d_R1_1_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv21336_7e0d_R1_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv21336_7e0d_R1_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv22504_7f3f_R4_1_I2 /\ Inv21336_7e0d_R1_1_I2 /\ HandleRequestVoteResponseAction => Inv21336_7e0d_R1_1_I2' BY DEF TypeOK,Inv22504_7f3f_R4_1_I2,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv21336_7e0d_R1_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv21336_7e0d_R1_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv21336_7e0d_R1_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv21336_7e0d_R1_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv21336_7e0d_R1_1_I2
  \* (Inv21336_7e0d_R1_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv21336_7e0d_R1_1_I2 /\ HandleAppendEntriesResponseAction => Inv21336_7e0d_R1_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv21336_7e0d_R1_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv17_ed8d_R0_1_I0
THEOREM L_4 == TypeOK /\ Inv15883_404d_R2_1_I2 /\ Inv28_5a2e_R2_2_I0 /\ Inv21336_7e0d_R1_1_I2 /\ Inv17_ed8d_R0_1_I0 /\ Next => Inv17_ed8d_R0_1_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv17_ed8d_R0_1_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv17_ed8d_R0_1_I0 /\ RequestVoteAction => Inv17_ed8d_R0_1_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv17_ed8d_R0_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv17_ed8d_R0_1_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv17_ed8d_R0_1_I0 /\ UpdateTermAction => Inv17_ed8d_R0_1_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv17_ed8d_R0_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv17_ed8d_R0_1_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv17_ed8d_R0_1_I0 /\ BecomeLeaderAction => Inv17_ed8d_R0_1_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv17_ed8d_R0_1_I0
  \* (Inv17_ed8d_R0_1_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv15883_404d_R2_1_I2 /\ Inv17_ed8d_R0_1_I0 /\ ClientRequestAction => Inv17_ed8d_R0_1_I0' BY DEF TypeOK,Inv15883_404d_R2_1_I2,ClientRequestAction,ClientRequest,Inv17_ed8d_R0_1_I0
  \* (Inv17_ed8d_R0_1_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv17_ed8d_R0_1_I0 /\ AppendEntriesAction => Inv17_ed8d_R0_1_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv17_ed8d_R0_1_I0
  \* (Inv17_ed8d_R0_1_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv17_ed8d_R0_1_I0 /\ HandleRequestVoteRequestAction => Inv17_ed8d_R0_1_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv17_ed8d_R0_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv17_ed8d_R0_1_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv28_5a2e_R2_2_I0 /\ Inv17_ed8d_R0_1_I0 /\ HandleRequestVoteResponseAction => Inv17_ed8d_R0_1_I0' BY DEF TypeOK,Inv28_5a2e_R2_2_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv17_ed8d_R0_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv17_ed8d_R0_1_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv21336_7e0d_R1_1_I2 /\ Inv17_ed8d_R0_1_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv17_ed8d_R0_1_I0' BY DEF TypeOK,Inv21336_7e0d_R1_1_I2,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv17_ed8d_R0_1_I0
  \* (Inv17_ed8d_R0_1_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv17_ed8d_R0_1_I0 /\ HandleAppendEntriesResponseAction => Inv17_ed8d_R0_1_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv17_ed8d_R0_1_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv15883_404d_R2_1_I2
THEOREM L_5 == TypeOK /\ Inv4_8e53_R5_0_I0 /\ Inv10_928b_R5_1_I1 /\ Inv42_3acc_R5_1_I1 /\ Inv6_42ac_R5_1_I1 /\ Inv4_8e53_R5_0_I0 /\ Inv15883_404d_R2_1_I2 /\ Next => Inv15883_404d_R2_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv15883_404d_R2_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv15883_404d_R2_1_I2 /\ RequestVoteAction => Inv15883_404d_R2_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv15883_404d_R2_1_I2,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) \/ (~((state[VARJ] = Leader))) \/ (~(votesGranted[VARI] \in Quorum)))'
      BY DEF Inv15883_404d_R2_1_I2, RequestVoteAction
    <2> QED
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv15883_404d_R2_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv15883_404d_R2_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv15883_404d_R2_1_I2 /\ UpdateTermAction => Inv15883_404d_R2_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv15883_404d_R2_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv15883_404d_R2_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv4_8e53_R5_0_I0 /\ Inv15883_404d_R2_1_I2 /\ BecomeLeaderAction => Inv15883_404d_R2_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv4_8e53_R5_0_I0,
                        Inv15883_404d_R2_1_I2,
                        TRUE,
                        NEW i \in Server,
                        BecomeLeader(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) \/ (~((state[VARJ] = Leader))) \/ (~(votesGranted[VARI] \in Quorum)))'
      BY DEF BecomeLeaderAction, Inv15883_404d_R2_1_I2
    <2> QED
      BY EmptyIntersectionImpliesNotBothQuorums, StaticQuorumsOverlap, FS_Intersection DEF TypeOK,Inv4_8e53_R5_0_I0,BecomeLeaderAction,BecomeLeader,Inv15883_404d_R2_1_I2
  \* (Inv15883_404d_R2_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv15883_404d_R2_1_I2 /\ ClientRequestAction => Inv15883_404d_R2_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv15883_404d_R2_1_I2
  \* (Inv15883_404d_R2_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv15883_404d_R2_1_I2 /\ AppendEntriesAction => Inv15883_404d_R2_1_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv15883_404d_R2_1_I2
  \* (Inv15883_404d_R2_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv15883_404d_R2_1_I2 /\ HandleRequestVoteRequestAction => Inv15883_404d_R2_1_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv15883_404d_R2_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv15883_404d_R2_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv10_928b_R5_1_I1 /\ Inv42_3acc_R5_1_I1 /\ Inv6_42ac_R5_1_I1 /\ Inv4_8e53_R5_0_I0 /\ Inv15883_404d_R2_1_I2 /\ HandleRequestVoteResponseAction => Inv15883_404d_R2_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv10_928b_R5_1_I1,
                        Inv42_3acc_R5_1_I1,
                        Inv6_42ac_R5_1_I1,
                        Inv4_8e53_R5_0_I0,
                        Inv15883_404d_R2_1_I2,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) \/ (~((state[VARJ] = Leader))) \/ (~(votesGranted[VARI] \in Quorum)))'
      BY DEF HandleRequestVoteResponseAction, Inv15883_404d_R2_1_I2
    <2> QED
      BY EmptyIntersectionImpliesNotBothQuorums, StaticQuorumsOverlap, FS_Intersection DEF TypeOK,Inv10_928b_R5_1_I1,Inv42_3acc_R5_1_I1,Inv6_42ac_R5_1_I1,Inv4_8e53_R5_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv15883_404d_R2_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv15883_404d_R2_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv15883_404d_R2_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv15883_404d_R2_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv15883_404d_R2_1_I2
  \* (Inv15883_404d_R2_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv15883_404d_R2_1_I2 /\ HandleAppendEntriesResponseAction => Inv15883_404d_R2_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv15883_404d_R2_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv4_8e53_R5_0_I0
THEOREM L_6 == TypeOK /\ Inv0_2c32_R8_1_I1 /\ Inv6_42ac_R5_1_I1 /\ Inv4_8e53_R5_0_I0 /\ Next => Inv4_8e53_R5_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv4_8e53_R5_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv0_2c32_R8_1_I1 /\ Inv4_8e53_R5_0_I0 /\ RequestVoteAction => Inv4_8e53_R5_0_I0' BY DEF TypeOK,Inv0_2c32_R8_1_I1,RequestVoteAction,RequestVote,Inv4_8e53_R5_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv4_8e53_R5_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv4_8e53_R5_0_I0 /\ UpdateTermAction => Inv4_8e53_R5_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv4_8e53_R5_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv4_8e53_R5_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv4_8e53_R5_0_I0 /\ BecomeLeaderAction => Inv4_8e53_R5_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv4_8e53_R5_0_I0
  \* (Inv4_8e53_R5_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv4_8e53_R5_0_I0 /\ ClientRequestAction => Inv4_8e53_R5_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv4_8e53_R5_0_I0
  \* (Inv4_8e53_R5_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv4_8e53_R5_0_I0 /\ AppendEntriesAction => Inv4_8e53_R5_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv4_8e53_R5_0_I0
  \* (Inv4_8e53_R5_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv4_8e53_R5_0_I0 /\ HandleRequestVoteRequestAction => Inv4_8e53_R5_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv4_8e53_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv4_8e53_R5_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv6_42ac_R5_1_I1 /\ Inv4_8e53_R5_0_I0 /\ HandleRequestVoteResponseAction => Inv4_8e53_R5_0_I0' BY DEF TypeOK,Inv6_42ac_R5_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv4_8e53_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv4_8e53_R5_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv4_8e53_R5_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv4_8e53_R5_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv4_8e53_R5_0_I0
  \* (Inv4_8e53_R5_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv4_8e53_R5_0_I0 /\ HandleAppendEntriesResponseAction => Inv4_8e53_R5_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv4_8e53_R5_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv6_42ac_R5_1_I1
\* Note: added Inv9_f533_R11_1_I0 extra support lemma.
THEOREM L_7 == TypeOK /\ Inv9_82b3_R10_1_I0 /\ Inv9_f533_R11_1_I0 /\ Inv0_e30e_R11_0_I1 /\ Inv6_42ac_R5_1_I1 /\ Next => Inv6_42ac_R5_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv6_42ac_R5_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv9_f533_R11_1_I0 /\ Inv6_42ac_R5_1_I1 /\ RequestVoteAction => Inv6_42ac_R5_1_I1' BY DEF TypeOK,Inv9_f533_R11_1_I0,RequestVoteAction,RequestVote,Inv6_42ac_R5_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6_42ac_R5_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv6_42ac_R5_1_I1 /\ UpdateTermAction => Inv6_42ac_R5_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv6_42ac_R5_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6_42ac_R5_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv6_42ac_R5_1_I1 /\ BecomeLeaderAction => Inv6_42ac_R5_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv6_42ac_R5_1_I1
  \* (Inv6_42ac_R5_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv6_42ac_R5_1_I1 /\ ClientRequestAction => Inv6_42ac_R5_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv6_42ac_R5_1_I1
  \* (Inv6_42ac_R5_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv6_42ac_R5_1_I1 /\ AppendEntriesAction => Inv6_42ac_R5_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv6_42ac_R5_1_I1
  \* (Inv6_42ac_R5_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv0_e30e_R11_0_I1 /\ Inv6_42ac_R5_1_I1 /\ HandleRequestVoteRequestAction => Inv6_42ac_R5_1_I1' BY DEF TypeOK,Inv0_e30e_R11_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv6_42ac_R5_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6_42ac_R5_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv9_82b3_R10_1_I0 /\ Inv6_42ac_R5_1_I1 /\ HandleRequestVoteResponseAction => Inv6_42ac_R5_1_I1' 
    BY AddingToQuorumRemainsQuorum, FS_Singleton, FS_Difference DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv9_82b3_R10_1_I0,Inv6_42ac_R5_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6_42ac_R5_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv6_42ac_R5_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv6_42ac_R5_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv6_42ac_R5_1_I1
  \* (Inv6_42ac_R5_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv6_42ac_R5_1_I1 /\ HandleAppendEntriesResponseAction => Inv6_42ac_R5_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv6_42ac_R5_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv0_e30e_R11_0_I1
THEOREM L_8 == TypeOK /\ Inv0_2c32_R8_1_I1 /\ Inv0_2c32_R8_1_I1 /\ Inv10_3715_R21_0_I0 /\ Inv0_e30e_R11_0_I1 /\ Next => Inv0_e30e_R11_0_I1'
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
      BY DEF LastTerm, TypeOK,Inv0_2c32_R8_1_I1,RequestVoteAction,RequestVote,Inv0_e30e_R11_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
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
  <1>7. TypeOK /\ Inv10_3715_R21_0_I0 /\ Inv0_e30e_R11_0_I1 /\ HandleRequestVoteResponseAction => Inv0_e30e_R11_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv10_3715_R21_0_I0,
                        Inv0_e30e_R11_0_I1,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server'
                 PROVE  (((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI )) \/ (((state[VARI] = Follower))))'
      BY DEF HandleRequestVoteResponseAction, Inv0_e30e_R11_0_I1
    <2> QED
      BY DEF TypeOK,Inv10_3715_R21_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv0_e30e_R11_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_e30e_R11_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv0_e30e_R11_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv0_e30e_R11_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv0_e30e_R11_0_I1
  \* (Inv0_e30e_R11_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv0_e30e_R11_0_I1 /\ HandleAppendEntriesResponseAction => Inv0_e30e_R11_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv0_e30e_R11_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv10_3715_R21_0_I0
THEOREM L_9 == TypeOK /\ Inv9_f533_R11_1_I0 /\ Inv9_f533_R11_1_I0 /\ Inv10_3715_R21_0_I0 /\ Next => Inv10_3715_R21_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv10_3715_R21_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv9_f533_R11_1_I0 /\ Inv10_3715_R21_0_I0 /\ RequestVoteAction => Inv10_3715_R21_0_I0' BY DEF TypeOK,Inv9_f533_R11_1_I0,RequestVoteAction,RequestVote,Inv10_3715_R21_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10_3715_R21_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv9_f533_R11_1_I0 /\ Inv10_3715_R21_0_I0 /\ UpdateTermAction => Inv10_3715_R21_0_I0' BY DEF TypeOK,Inv9_f533_R11_1_I0,UpdateTermAction,UpdateTerm,Inv10_3715_R21_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10_3715_R21_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv10_3715_R21_0_I0 /\ BecomeLeaderAction => Inv10_3715_R21_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv10_3715_R21_0_I0
  \* (Inv10_3715_R21_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv10_3715_R21_0_I0 /\ ClientRequestAction => Inv10_3715_R21_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv10_3715_R21_0_I0
  \* (Inv10_3715_R21_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv10_3715_R21_0_I0 /\ AppendEntriesAction => Inv10_3715_R21_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv10_3715_R21_0_I0
  \* (Inv10_3715_R21_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv10_3715_R21_0_I0 /\ HandleRequestVoteRequestAction => Inv10_3715_R21_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_3715_R21_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_3715_R21_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv10_3715_R21_0_I0 /\ HandleRequestVoteResponseAction => Inv10_3715_R21_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv10_3715_R21_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_3715_R21_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv10_3715_R21_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv10_3715_R21_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv10_3715_R21_0_I0
  \* (Inv10_3715_R21_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv10_3715_R21_0_I0 /\ HandleAppendEntriesResponseAction => Inv10_3715_R21_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv10_3715_R21_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv9_f533_R11_1_I0
THEOREM L_10 == TypeOK /\ Inv9_f533_R11_1_I0 /\ Next => Inv9_f533_R11_1_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv9_f533_R11_1_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv9_f533_R11_1_I0 /\ RequestVoteAction => Inv9_f533_R11_1_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv9_f533_R11_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv9_f533_R11_1_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv9_f533_R11_1_I0 /\ UpdateTermAction => Inv9_f533_R11_1_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv9_f533_R11_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv9_f533_R11_1_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv9_f533_R11_1_I0 /\ BecomeLeaderAction => Inv9_f533_R11_1_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv9_f533_R11_1_I0
  \* (Inv9_f533_R11_1_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv9_f533_R11_1_I0 /\ ClientRequestAction => Inv9_f533_R11_1_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv9_f533_R11_1_I0
  \* (Inv9_f533_R11_1_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv9_f533_R11_1_I0 /\ AppendEntriesAction => Inv9_f533_R11_1_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv9_f533_R11_1_I0
  \* (Inv9_f533_R11_1_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv9_f533_R11_1_I0 /\ HandleRequestVoteRequestAction => Inv9_f533_R11_1_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_f533_R11_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv9_f533_R11_1_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv9_f533_R11_1_I0 /\ HandleRequestVoteResponseAction => Inv9_f533_R11_1_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv9_f533_R11_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv9_f533_R11_1_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv9_f533_R11_1_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv9_f533_R11_1_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv9_f533_R11_1_I0
  \* (Inv9_f533_R11_1_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv9_f533_R11_1_I0 /\ HandleAppendEntriesResponseAction => Inv9_f533_R11_1_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv9_f533_R11_1_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv0_2c32_R8_1_I1
THEOREM L_11 == TypeOK /\ Inv9_f533_R11_1_I0 /\ Inv0_2c32_R8_1_I1 /\ Next => Inv0_2c32_R8_1_I1'
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
  <1>7. TypeOK /\ Inv9_f533_R11_1_I0 /\ Inv0_2c32_R8_1_I1 /\ HandleRequestVoteResponseAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,Inv9_f533_R11_1_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv0_2c32_R8_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_2c32_R8_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv0_2c32_R8_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv0_2c32_R8_1_I1
  \* (Inv0_2c32_R8_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv0_2c32_R8_1_I1 /\ HandleAppendEntriesResponseAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv0_2c32_R8_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv10_928b_R5_1_I1
THEOREM L_12 == TypeOK /\ Inv877_09bb_R9_0_I1 /\ Inv10_928b_R5_1_I1 /\ Next => Inv10_928b_R5_1_I1'
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
  <1>7. TypeOK /\ Inv877_09bb_R9_0_I1 /\ Inv10_928b_R5_1_I1 /\ HandleRequestVoteResponseAction => Inv10_928b_R5_1_I1' BY DEF TypeOK,Inv877_09bb_R9_0_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv10_928b_R5_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_928b_R5_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv10_928b_R5_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv10_928b_R5_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv10_928b_R5_1_I1
  \* (Inv10_928b_R5_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv10_928b_R5_1_I1 /\ HandleAppendEntriesResponseAction => Inv10_928b_R5_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv10_928b_R5_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv877_09bb_R9_0_I1
THEOREM L_13 == TypeOK /\ Inv480_fe26_R17_0_I1 /\ Inv877_09bb_R9_0_I1 /\ Next => Inv877_09bb_R9_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv877_09bb_R9_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv877_09bb_R9_0_I1 /\ RequestVoteAction => Inv877_09bb_R9_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv877_09bb_R9_0_I1,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARREQVRES \in requestVoteResponseMsgs'
                 PROVE  (~(VARREQVRES.mdest = VARI) \/ (~(votesGranted[VARI] = {})))'
      BY DEF Inv877_09bb_R9_0_I1, RequestVoteAction
    <2> QED
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv877_09bb_R9_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv877_09bb_R9_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv877_09bb_R9_0_I1 /\ UpdateTermAction => Inv877_09bb_R9_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv877_09bb_R9_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv877_09bb_R9_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv877_09bb_R9_0_I1 /\ BecomeLeaderAction => Inv877_09bb_R9_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv877_09bb_R9_0_I1
  \* (Inv877_09bb_R9_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv877_09bb_R9_0_I1 /\ ClientRequestAction => Inv877_09bb_R9_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv877_09bb_R9_0_I1
  \* (Inv877_09bb_R9_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv877_09bb_R9_0_I1 /\ AppendEntriesAction => Inv877_09bb_R9_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv877_09bb_R9_0_I1
  \* (Inv877_09bb_R9_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv480_fe26_R17_0_I1 /\ Inv877_09bb_R9_0_I1 /\ HandleRequestVoteRequestAction => Inv877_09bb_R9_0_I1' BY DEF TypeOK,Inv480_fe26_R17_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv877_09bb_R9_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv877_09bb_R9_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv877_09bb_R9_0_I1 /\ HandleRequestVoteResponseAction => Inv877_09bb_R9_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv877_09bb_R9_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv877_09bb_R9_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv877_09bb_R9_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv877_09bb_R9_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv877_09bb_R9_0_I1
  \* (Inv877_09bb_R9_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv877_09bb_R9_0_I1 /\ HandleAppendEntriesResponseAction => Inv877_09bb_R9_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv877_09bb_R9_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv480_fe26_R17_0_I1
THEOREM L_14 == TypeOK /\ Inv480_fe26_R17_0_I1 /\ Next => Inv480_fe26_R17_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv480_fe26_R17_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv480_fe26_R17_0_I1 /\ RequestVoteAction => Inv480_fe26_R17_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv480_fe26_R17_0_I1,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARREQVM \in requestVoteRequestMsgs'
                 PROVE  (~(VARREQVM.msource = VARI) \/ (~(votesGranted[VARI] = {})))'
      BY DEF Inv480_fe26_R17_0_I1, RequestVoteAction
    <2>1. CASE (VARREQVM.msource # VARI)
       BY <2>1, FS_Singleton, FS_Difference, FS_EmptySet, FS_Intersection DEF LastTerm, TypeOK,RequestVoteAction,RequestVote,Inv480_fe26_R17_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>2. CASE VARREQVM.msource = VARI /\ VARREQVM \in requestVoteRequestMsgs
        BY <2>2, FS_Singleton, FS_EmptySet, FS_Intersection DEF LastTerm, TypeOK,RequestVoteAction,RequestVote,Inv480_fe26_R17_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>3. CASE VARREQVM.msource = VARI /\ VARREQVM \notin requestVoteRequestMsgs /\ VARI = i
        BY <2>3, FS_Singleton, FS_EmptySet, FS_Intersection DEF LastTerm, TypeOK,RequestVoteAction,RequestVote,Inv480_fe26_R17_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>4. CASE VARREQVM.msource = VARI /\ VARREQVM \notin requestVoteRequestMsgs /\ VARI # i
        BY <2>4, FS_Singleton, FS_EmptySet, FS_Intersection DEF LastTerm, TypeOK,RequestVoteAction,RequestVote,Inv480_fe26_R17_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType      
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, FS_Singleton, FS_EmptySet, FS_Intersection DEF LastTerm, TypeOK,RequestVoteAction,RequestVote,Inv480_fe26_R17_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv480_fe26_R17_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv480_fe26_R17_0_I1 /\ UpdateTermAction => Inv480_fe26_R17_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv480_fe26_R17_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv480_fe26_R17_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv480_fe26_R17_0_I1 /\ BecomeLeaderAction => Inv480_fe26_R17_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv480_fe26_R17_0_I1
  \* (Inv480_fe26_R17_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv480_fe26_R17_0_I1 /\ ClientRequestAction => Inv480_fe26_R17_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv480_fe26_R17_0_I1
  \* (Inv480_fe26_R17_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv480_fe26_R17_0_I1 /\ AppendEntriesAction => Inv480_fe26_R17_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv480_fe26_R17_0_I1
  \* (Inv480_fe26_R17_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv480_fe26_R17_0_I1 /\ HandleRequestVoteRequestAction => Inv480_fe26_R17_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv480_fe26_R17_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv480_fe26_R17_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv480_fe26_R17_0_I1 /\ HandleRequestVoteResponseAction => Inv480_fe26_R17_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv480_fe26_R17_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv480_fe26_R17_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv480_fe26_R17_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv480_fe26_R17_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv480_fe26_R17_0_I1
  \* (Inv480_fe26_R17_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv480_fe26_R17_0_I1 /\ HandleAppendEntriesResponseAction => Inv480_fe26_R17_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv480_fe26_R17_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv42_3acc_R5_1_I1
THEOREM L_15 == TypeOK /\ Inv42_3acc_R5_1_I1 /\ Next => Inv42_3acc_R5_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv42_3acc_R5_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv42_3acc_R5_1_I1 /\ RequestVoteAction => Inv42_3acc_R5_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv42_3acc_R5_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv42_3acc_R5_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv42_3acc_R5_1_I1 /\ UpdateTermAction => Inv42_3acc_R5_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv42_3acc_R5_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv42_3acc_R5_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv42_3acc_R5_1_I1 /\ BecomeLeaderAction => Inv42_3acc_R5_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv42_3acc_R5_1_I1
  \* (Inv42_3acc_R5_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv42_3acc_R5_1_I1 /\ ClientRequestAction => Inv42_3acc_R5_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv42_3acc_R5_1_I1
  \* (Inv42_3acc_R5_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv42_3acc_R5_1_I1 /\ AppendEntriesAction => Inv42_3acc_R5_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv42_3acc_R5_1_I1
  \* (Inv42_3acc_R5_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv42_3acc_R5_1_I1 /\ HandleRequestVoteRequestAction => Inv42_3acc_R5_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv42_3acc_R5_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv42_3acc_R5_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv42_3acc_R5_1_I1 /\ HandleRequestVoteResponseAction => Inv42_3acc_R5_1_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv42_3acc_R5_1_I1,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server'
                 PROVE  ((votesGranted[VARI] \in Quorum) \/ (~((state[VARI] = Leader))))'
      BY DEF HandleRequestVoteResponseAction, Inv42_3acc_R5_1_I1
    <2> QED
      BY FS_Singleton, FS_Union, AddingToQuorumRemainsQuorum DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv42_3acc_R5_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv42_3acc_R5_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv42_3acc_R5_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv42_3acc_R5_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv42_3acc_R5_1_I1
  \* (Inv42_3acc_R5_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv42_3acc_R5_1_I1 /\ HandleAppendEntriesResponseAction => Inv42_3acc_R5_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv42_3acc_R5_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv28_5a2e_R2_2_I0
THEOREM L_16 == TypeOK /\ Inv70_1e2e_R6_3_I1 /\ Inv15883_404d_R2_1_I2 /\ Inv109_4308_R6_1_I1 /\ Inv6_42ac_R5_1_I1 /\ Inv42_3acc_R5_1_I1 /\ Inv4_8e53_R5_0_I0 /\ Inv672_4aa6_R6_2_I1 /\ Inv4_c57a_R6_2_I1 /\ Inv1082_1f30_R6_2_I1 /\ Inv22504_7f3f_R4_1_I2 /\ Inv28_5a2e_R2_2_I0 /\ Next => Inv28_5a2e_R2_2_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv28_5a2e_R2_2_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv70_1e2e_R6_3_I1 /\ Inv28_5a2e_R2_2_I0 /\ RequestVoteAction => Inv28_5a2e_R2_2_I0' BY DEF TypeOK,Inv70_1e2e_R6_3_I1,RequestVoteAction,RequestVote,Inv28_5a2e_R2_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv28_5a2e_R2_2_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv28_5a2e_R2_2_I0 /\ UpdateTermAction => Inv28_5a2e_R2_2_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv28_5a2e_R2_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv28_5a2e_R2_2_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv28_5a2e_R2_2_I0 /\ BecomeLeaderAction => Inv28_5a2e_R2_2_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv28_5a2e_R2_2_I0
  \* (Inv28_5a2e_R2_2_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv15883_404d_R2_1_I2 /\ Inv109_4308_R6_1_I1 /\ Inv6_42ac_R5_1_I1 /\ Inv42_3acc_R5_1_I1 /\ Inv4_8e53_R5_0_I0 /\ Inv28_5a2e_R2_2_I0 /\ ClientRequestAction => Inv28_5a2e_R2_2_I0' BY DEF TypeOK,Inv15883_404d_R2_1_I2,Inv109_4308_R6_1_I1,Inv6_42ac_R5_1_I1,Inv42_3acc_R5_1_I1,Inv4_8e53_R5_0_I0,ClientRequestAction,ClientRequest,Inv28_5a2e_R2_2_I0
  \* (Inv28_5a2e_R2_2_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv28_5a2e_R2_2_I0 /\ AppendEntriesAction => Inv28_5a2e_R2_2_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv28_5a2e_R2_2_I0
  \* (Inv28_5a2e_R2_2_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv672_4aa6_R6_2_I1 /\ Inv4_c57a_R6_2_I1 /\ Inv1082_1f30_R6_2_I1 /\ Inv28_5a2e_R2_2_I0 /\ HandleRequestVoteRequestAction => Inv28_5a2e_R2_2_I0' BY DEF TypeOK,Inv672_4aa6_R6_2_I1,Inv4_c57a_R6_2_I1,Inv1082_1f30_R6_2_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv28_5a2e_R2_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv28_5a2e_R2_2_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv28_5a2e_R2_2_I0 /\ HandleRequestVoteResponseAction => Inv28_5a2e_R2_2_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv28_5a2e_R2_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv28_5a2e_R2_2_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv22504_7f3f_R4_1_I2 /\ Inv28_5a2e_R2_2_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv28_5a2e_R2_2_I0' BY DEF TypeOK,Inv22504_7f3f_R4_1_I2,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv28_5a2e_R2_2_I0
  \* (Inv28_5a2e_R2_2_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv28_5a2e_R2_2_I0 /\ HandleAppendEntriesResponseAction => Inv28_5a2e_R2_2_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv28_5a2e_R2_2_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv22504_7f3f_R4_1_I2
THEOREM L_17 == TypeOK /\ Inv70_1e2e_R6_3_I1 /\ Inv28_5a2e_R2_2_I0 /\ Inv7027_6cb8_R7_1_I2 /\ Inv1082_1f30_R6_2_I1 /\ Inv40_2a9c_R7_1_I2 /\ Inv22504_7f3f_R4_1_I2 /\ Next => Inv22504_7f3f_R4_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv22504_7f3f_R4_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv70_1e2e_R6_3_I1 /\ Inv22504_7f3f_R4_1_I2 /\ RequestVoteAction => Inv22504_7f3f_R4_1_I2' BY DEF TypeOK,Inv70_1e2e_R6_3_I1,RequestVoteAction,RequestVote,Inv22504_7f3f_R4_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv22504_7f3f_R4_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv22504_7f3f_R4_1_I2 /\ UpdateTermAction => Inv22504_7f3f_R4_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv22504_7f3f_R4_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv22504_7f3f_R4_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv22504_7f3f_R4_1_I2 /\ BecomeLeaderAction => Inv22504_7f3f_R4_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv22504_7f3f_R4_1_I2
  \* (Inv22504_7f3f_R4_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv22504_7f3f_R4_1_I2 /\ ClientRequestAction => Inv22504_7f3f_R4_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv22504_7f3f_R4_1_I2
  \* (Inv22504_7f3f_R4_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv28_5a2e_R2_2_I0 /\ Inv22504_7f3f_R4_1_I2 /\ AppendEntriesAction => Inv22504_7f3f_R4_1_I2' BY DEF TypeOK,Inv28_5a2e_R2_2_I0,AppendEntriesAction,AppendEntries,Inv22504_7f3f_R4_1_I2
  \* (Inv22504_7f3f_R4_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv7027_6cb8_R7_1_I2 /\ Inv1082_1f30_R6_2_I1 /\ Inv40_2a9c_R7_1_I2 /\ Inv22504_7f3f_R4_1_I2 /\ HandleRequestVoteRequestAction => Inv22504_7f3f_R4_1_I2' BY DEF TypeOK,Inv7027_6cb8_R7_1_I2,Inv1082_1f30_R6_2_I1,Inv40_2a9c_R7_1_I2,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv22504_7f3f_R4_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv22504_7f3f_R4_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv22504_7f3f_R4_1_I2 /\ HandleRequestVoteResponseAction => Inv22504_7f3f_R4_1_I2' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv22504_7f3f_R4_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv22504_7f3f_R4_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv22504_7f3f_R4_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv22504_7f3f_R4_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv22504_7f3f_R4_1_I2
  \* (Inv22504_7f3f_R4_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv22504_7f3f_R4_1_I2 /\ HandleAppendEntriesResponseAction => Inv22504_7f3f_R4_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv22504_7f3f_R4_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv7027_6cb8_R7_1_I2
THEOREM L_18 == TypeOK /\ Inv877_09bb_R9_0_I1 /\ Inv480_fe26_R17_0_I1 /\ Inv7027_6cb8_R7_1_I2 /\ Next => Inv7027_6cb8_R7_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv7027_6cb8_R7_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv7027_6cb8_R7_1_I2 /\ RequestVoteAction => Inv7027_6cb8_R7_1_I2' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv7027_6cb8_R7_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7027_6cb8_R7_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv877_09bb_R9_0_I1 /\ Inv7027_6cb8_R7_1_I2 /\ UpdateTermAction => Inv7027_6cb8_R7_1_I2' BY DEF TypeOK,Inv877_09bb_R9_0_I1,UpdateTermAction,UpdateTerm,Inv7027_6cb8_R7_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7027_6cb8_R7_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv7027_6cb8_R7_1_I2 /\ BecomeLeaderAction => Inv7027_6cb8_R7_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv7027_6cb8_R7_1_I2
  \* (Inv7027_6cb8_R7_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv7027_6cb8_R7_1_I2 /\ ClientRequestAction => Inv7027_6cb8_R7_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv7027_6cb8_R7_1_I2
  \* (Inv7027_6cb8_R7_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv7027_6cb8_R7_1_I2 /\ AppendEntriesAction => Inv7027_6cb8_R7_1_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv7027_6cb8_R7_1_I2
  \* (Inv7027_6cb8_R7_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv480_fe26_R17_0_I1 /\ Inv7027_6cb8_R7_1_I2 /\ HandleRequestVoteRequestAction => Inv7027_6cb8_R7_1_I2' BY DEF TypeOK,Inv480_fe26_R17_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7027_6cb8_R7_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7027_6cb8_R7_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv7027_6cb8_R7_1_I2 /\ HandleRequestVoteResponseAction => Inv7027_6cb8_R7_1_I2' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv7027_6cb8_R7_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7027_6cb8_R7_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv7027_6cb8_R7_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv7027_6cb8_R7_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv7027_6cb8_R7_1_I2
  \* (Inv7027_6cb8_R7_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv7027_6cb8_R7_1_I2 /\ HandleAppendEntriesResponseAction => Inv7027_6cb8_R7_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv7027_6cb8_R7_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv1082_1f30_R6_2_I1
THEOREM L_19 == TypeOK /\ Inv1082_1f30_R6_2_I1 /\ Next => Inv1082_1f30_R6_2_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv1082_1f30_R6_2_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv1082_1f30_R6_2_I1 /\ RequestVoteAction => Inv1082_1f30_R6_2_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv1082_1f30_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1082_1f30_R6_2_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv1082_1f30_R6_2_I1 /\ UpdateTermAction => Inv1082_1f30_R6_2_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv1082_1f30_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1082_1f30_R6_2_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv1082_1f30_R6_2_I1 /\ BecomeLeaderAction => Inv1082_1f30_R6_2_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv1082_1f30_R6_2_I1
  \* (Inv1082_1f30_R6_2_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv1082_1f30_R6_2_I1 /\ ClientRequestAction => Inv1082_1f30_R6_2_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv1082_1f30_R6_2_I1
  \* (Inv1082_1f30_R6_2_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv1082_1f30_R6_2_I1 /\ AppendEntriesAction => Inv1082_1f30_R6_2_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv1082_1f30_R6_2_I1
  \* (Inv1082_1f30_R6_2_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv1082_1f30_R6_2_I1 /\ HandleRequestVoteRequestAction => Inv1082_1f30_R6_2_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv1082_1f30_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1082_1f30_R6_2_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv1082_1f30_R6_2_I1 /\ HandleRequestVoteResponseAction => Inv1082_1f30_R6_2_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv1082_1f30_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1082_1f30_R6_2_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv1082_1f30_R6_2_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv1082_1f30_R6_2_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv1082_1f30_R6_2_I1
  \* (Inv1082_1f30_R6_2_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv1082_1f30_R6_2_I1 /\ HandleAppendEntriesResponseAction => Inv1082_1f30_R6_2_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv1082_1f30_R6_2_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv40_2a9c_R7_1_I2
THEOREM L_20 == TypeOK /\ Inv1152_5d57_R18_0_I1 /\ Inv8_441b_R14_1_I1 /\ Inv40_2a9c_R7_1_I2 /\ Next => Inv40_2a9c_R7_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv40_2a9c_R7_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv40_2a9c_R7_1_I2 /\ RequestVoteAction => Inv40_2a9c_R7_1_I2' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv40_2a9c_R7_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv40_2a9c_R7_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv40_2a9c_R7_1_I2 /\ UpdateTermAction => Inv40_2a9c_R7_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv40_2a9c_R7_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv40_2a9c_R7_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv40_2a9c_R7_1_I2 /\ BecomeLeaderAction => Inv40_2a9c_R7_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv40_2a9c_R7_1_I2
  \* (Inv40_2a9c_R7_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv40_2a9c_R7_1_I2 /\ ClientRequestAction => Inv40_2a9c_R7_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv40_2a9c_R7_1_I2
  \* (Inv40_2a9c_R7_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv1152_5d57_R18_0_I1 /\ Inv8_441b_R14_1_I1 /\ Inv40_2a9c_R7_1_I2 /\ AppendEntriesAction => Inv40_2a9c_R7_1_I2' BY DEF TypeOK,Inv1152_5d57_R18_0_I1,Inv8_441b_R14_1_I1,AppendEntriesAction,AppendEntries,Inv40_2a9c_R7_1_I2
  \* (Inv40_2a9c_R7_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv40_2a9c_R7_1_I2 /\ HandleRequestVoteRequestAction => Inv40_2a9c_R7_1_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv40_2a9c_R7_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv40_2a9c_R7_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv40_2a9c_R7_1_I2 /\ HandleRequestVoteResponseAction => Inv40_2a9c_R7_1_I2' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv40_2a9c_R7_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv40_2a9c_R7_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv40_2a9c_R7_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv40_2a9c_R7_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv40_2a9c_R7_1_I2
  \* (Inv40_2a9c_R7_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv40_2a9c_R7_1_I2 /\ HandleAppendEntriesResponseAction => Inv40_2a9c_R7_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv40_2a9c_R7_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv1152_5d57_R18_0_I1
THEOREM L_21 == TypeOK /\ Inv13_c904_R12_0_I0 /\ Inv1152_5d57_R18_0_I1 /\ Next => Inv1152_5d57_R18_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv1152_5d57_R18_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv1152_5d57_R18_0_I1 /\ RequestVoteAction => Inv1152_5d57_R18_0_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv1152_5d57_R18_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1152_5d57_R18_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv1152_5d57_R18_0_I1 /\ UpdateTermAction => Inv1152_5d57_R18_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv1152_5d57_R18_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1152_5d57_R18_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv1152_5d57_R18_0_I1 /\ BecomeLeaderAction => Inv1152_5d57_R18_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv1152_5d57_R18_0_I1
  \* (Inv1152_5d57_R18_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv1152_5d57_R18_0_I1 /\ ClientRequestAction => Inv1152_5d57_R18_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv1152_5d57_R18_0_I1
  \* (Inv1152_5d57_R18_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv1152_5d57_R18_0_I1 /\ AppendEntriesAction => Inv1152_5d57_R18_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv1152_5d57_R18_0_I1
  \* (Inv1152_5d57_R18_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv1152_5d57_R18_0_I1 /\ HandleRequestVoteRequestAction => Inv1152_5d57_R18_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv1152_5d57_R18_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1152_5d57_R18_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv1152_5d57_R18_0_I1 /\ HandleRequestVoteResponseAction => Inv1152_5d57_R18_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv1152_5d57_R18_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1152_5d57_R18_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv13_c904_R12_0_I0 /\ Inv1152_5d57_R18_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv1152_5d57_R18_0_I1' BY DEF TypeOK,Inv13_c904_R12_0_I0,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv1152_5d57_R18_0_I1
  \* (Inv1152_5d57_R18_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv1152_5d57_R18_0_I1 /\ HandleAppendEntriesResponseAction => Inv1152_5d57_R18_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv1152_5d57_R18_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv13_c904_R12_0_I0
THEOREM L_22 == TypeOK /\ Inv21_a5e5_R23_0_I0 /\ Inv13_c904_R12_0_I0 /\ Next => Inv13_c904_R12_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv13_c904_R12_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv13_c904_R12_0_I0 /\ RequestVoteAction => Inv13_c904_R12_0_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv13_c904_R12_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv13_c904_R12_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv13_c904_R12_0_I0 /\ UpdateTermAction => Inv13_c904_R12_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv13_c904_R12_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv13_c904_R12_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv13_c904_R12_0_I0 /\ BecomeLeaderAction => Inv13_c904_R12_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv13_c904_R12_0_I0
  \* (Inv13_c904_R12_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv13_c904_R12_0_I0 /\ ClientRequestAction => Inv13_c904_R12_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv13_c904_R12_0_I0
  \* (Inv13_c904_R12_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv21_a5e5_R23_0_I0 /\ Inv13_c904_R12_0_I0 /\ AppendEntriesAction => Inv13_c904_R12_0_I0' BY DEF TypeOK,Inv21_a5e5_R23_0_I0,AppendEntriesAction,AppendEntries,Inv13_c904_R12_0_I0
  \* (Inv13_c904_R12_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv13_c904_R12_0_I0 /\ HandleRequestVoteRequestAction => Inv13_c904_R12_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv13_c904_R12_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv13_c904_R12_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv13_c904_R12_0_I0 /\ HandleRequestVoteResponseAction => Inv13_c904_R12_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv13_c904_R12_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv13_c904_R12_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv13_c904_R12_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv13_c904_R12_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv13_c904_R12_0_I0
  \* (Inv13_c904_R12_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv13_c904_R12_0_I0 /\ HandleAppendEntriesResponseAction => Inv13_c904_R12_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv13_c904_R12_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv21_a5e5_R23_0_I0
THEOREM L_23 == TypeOK /\ Inv13_c904_R12_0_I0 /\ Inv21_a5e5_R23_0_I0 /\ Next => Inv21_a5e5_R23_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv21_a5e5_R23_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv21_a5e5_R23_0_I0 /\ RequestVoteAction => Inv21_a5e5_R23_0_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv21_a5e5_R23_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv21_a5e5_R23_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv21_a5e5_R23_0_I0 /\ UpdateTermAction => Inv21_a5e5_R23_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv21_a5e5_R23_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv21_a5e5_R23_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv21_a5e5_R23_0_I0 /\ BecomeLeaderAction => Inv21_a5e5_R23_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv21_a5e5_R23_0_I0
  \* (Inv21_a5e5_R23_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv21_a5e5_R23_0_I0 /\ ClientRequestAction => Inv21_a5e5_R23_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv21_a5e5_R23_0_I0
  \* (Inv21_a5e5_R23_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv21_a5e5_R23_0_I0 /\ AppendEntriesAction => Inv21_a5e5_R23_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv21_a5e5_R23_0_I0
  \* (Inv21_a5e5_R23_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv21_a5e5_R23_0_I0 /\ HandleRequestVoteRequestAction => Inv21_a5e5_R23_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv21_a5e5_R23_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv21_a5e5_R23_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv21_a5e5_R23_0_I0 /\ HandleRequestVoteResponseAction => Inv21_a5e5_R23_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv21_a5e5_R23_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv21_a5e5_R23_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv13_c904_R12_0_I0 /\ Inv21_a5e5_R23_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv21_a5e5_R23_0_I0' BY DEF TypeOK,Inv13_c904_R12_0_I0,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv21_a5e5_R23_0_I0
  \* (Inv21_a5e5_R23_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv21_a5e5_R23_0_I0 /\ HandleAppendEntriesResponseAction => Inv21_a5e5_R23_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv21_a5e5_R23_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv8_441b_R14_1_I1
THEOREM L_24 == TypeOK /\ Inv0_e30e_R11_0_I1 /\ Inv6346_3776_R25_0_I2 /\ Inv0_2c32_R8_1_I1 /\ Inv8_441b_R14_1_I1 /\ Next => Inv8_441b_R14_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv8_441b_R14_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv8_441b_R14_1_I1 /\ RequestVoteAction => Inv8_441b_R14_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv8_441b_R14_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv8_441b_R14_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv8_441b_R14_1_I1 /\ UpdateTermAction => Inv8_441b_R14_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv8_441b_R14_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv8_441b_R14_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv0_e30e_R11_0_I1 /\ Inv6346_3776_R25_0_I2 /\ Inv0_2c32_R8_1_I1 /\ Inv8_441b_R14_1_I1 /\ BecomeLeaderAction => Inv8_441b_R14_1_I1' BY DEF TypeOK,Inv0_e30e_R11_0_I1,Inv6346_3776_R25_0_I2,Inv0_2c32_R8_1_I1,BecomeLeaderAction,BecomeLeader,Inv8_441b_R14_1_I1
  \* (Inv8_441b_R14_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv8_441b_R14_1_I1 /\ ClientRequestAction => Inv8_441b_R14_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv8_441b_R14_1_I1
  \* (Inv8_441b_R14_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv8_441b_R14_1_I1 /\ AppendEntriesAction => Inv8_441b_R14_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv8_441b_R14_1_I1
  \* (Inv8_441b_R14_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv8_441b_R14_1_I1 /\ HandleRequestVoteRequestAction => Inv8_441b_R14_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv8_441b_R14_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv8_441b_R14_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv8_441b_R14_1_I1 /\ HandleRequestVoteResponseAction => Inv8_441b_R14_1_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv8_441b_R14_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv8_441b_R14_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv8_441b_R14_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv8_441b_R14_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv8_441b_R14_1_I1
  \* (Inv8_441b_R14_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv8_441b_R14_1_I1 /\ HandleAppendEntriesResponseAction => Inv8_441b_R14_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv8_441b_R14_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv6346_3776_R25_0_I2
THEOREM L_25 == TypeOK /\ Inv2_12a2_R34_1_I1 /\ Inv877_09bb_R9_0_I1 /\ Inv6346_3776_R25_0_I2 /\ Next => Inv6346_3776_R25_0_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv6346_3776_R25_0_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv2_12a2_R34_1_I1 /\ Inv6346_3776_R25_0_I2 /\ RequestVoteAction => Inv6346_3776_R25_0_I2' BY DEF TypeOK,Inv2_12a2_R34_1_I1,RequestVoteAction,RequestVote,Inv6346_3776_R25_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6346_3776_R25_0_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv6346_3776_R25_0_I2 /\ UpdateTermAction => Inv6346_3776_R25_0_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv6346_3776_R25_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6346_3776_R25_0_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv6346_3776_R25_0_I2 /\ BecomeLeaderAction => Inv6346_3776_R25_0_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv6346_3776_R25_0_I2
  \* (Inv6346_3776_R25_0_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv6346_3776_R25_0_I2 /\ ClientRequestAction => Inv6346_3776_R25_0_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv6346_3776_R25_0_I2
  \* (Inv6346_3776_R25_0_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv6346_3776_R25_0_I2 /\ AppendEntriesAction => Inv6346_3776_R25_0_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv6346_3776_R25_0_I2
  \* (Inv6346_3776_R25_0_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv6346_3776_R25_0_I2 /\ HandleRequestVoteRequestAction => Inv6346_3776_R25_0_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv6346_3776_R25_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6346_3776_R25_0_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv877_09bb_R9_0_I1 /\ Inv6346_3776_R25_0_I2 /\ HandleRequestVoteResponseAction => Inv6346_3776_R25_0_I2' BY DEF TypeOK,Inv877_09bb_R9_0_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv6346_3776_R25_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6346_3776_R25_0_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv6346_3776_R25_0_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv6346_3776_R25_0_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv6346_3776_R25_0_I2
  \* (Inv6346_3776_R25_0_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv6346_3776_R25_0_I2 /\ HandleAppendEntriesResponseAction => Inv6346_3776_R25_0_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv6346_3776_R25_0_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv2_12a2_R34_1_I1
THEOREM L_26 == TypeOK /\ Inv2_12a2_R34_1_I1 /\ Next => Inv2_12a2_R34_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv2_12a2_R34_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv2_12a2_R34_1_I1 /\ RequestVoteAction => Inv2_12a2_R34_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv2_12a2_R34_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv2_12a2_R34_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv2_12a2_R34_1_I1 /\ UpdateTermAction => Inv2_12a2_R34_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv2_12a2_R34_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv2_12a2_R34_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv2_12a2_R34_1_I1 /\ BecomeLeaderAction => Inv2_12a2_R34_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv2_12a2_R34_1_I1
  \* (Inv2_12a2_R34_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv2_12a2_R34_1_I1 /\ ClientRequestAction => Inv2_12a2_R34_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv2_12a2_R34_1_I1
  \* (Inv2_12a2_R34_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv2_12a2_R34_1_I1 /\ AppendEntriesAction => Inv2_12a2_R34_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv2_12a2_R34_1_I1
  \* (Inv2_12a2_R34_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv2_12a2_R34_1_I1 /\ HandleRequestVoteRequestAction => Inv2_12a2_R34_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv2_12a2_R34_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv2_12a2_R34_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv2_12a2_R34_1_I1 /\ HandleRequestVoteResponseAction => Inv2_12a2_R34_1_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv2_12a2_R34_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv2_12a2_R34_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv2_12a2_R34_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv2_12a2_R34_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv2_12a2_R34_1_I1
  \* (Inv2_12a2_R34_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv2_12a2_R34_1_I1 /\ HandleAppendEntriesResponseAction => Inv2_12a2_R34_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv2_12a2_R34_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv70_1e2e_R6_3_I1
THEOREM L_27 == TypeOK /\ Inv5_9e78_R16_0_I0 /\ Inv70_1e2e_R6_3_I1 /\ Next => Inv70_1e2e_R6_3_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv70_1e2e_R6_3_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv70_1e2e_R6_3_I1 /\ RequestVoteAction => Inv70_1e2e_R6_3_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv70_1e2e_R6_3_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv70_1e2e_R6_3_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv70_1e2e_R6_3_I1 /\ UpdateTermAction => Inv70_1e2e_R6_3_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv70_1e2e_R6_3_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv70_1e2e_R6_3_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv70_1e2e_R6_3_I1 /\ BecomeLeaderAction => Inv70_1e2e_R6_3_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv70_1e2e_R6_3_I1
  \* (Inv70_1e2e_R6_3_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv70_1e2e_R6_3_I1 /\ ClientRequestAction => Inv70_1e2e_R6_3_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv70_1e2e_R6_3_I1
  \* (Inv70_1e2e_R6_3_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv70_1e2e_R6_3_I1 /\ AppendEntriesAction => Inv70_1e2e_R6_3_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv70_1e2e_R6_3_I1
  \* (Inv70_1e2e_R6_3_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv5_9e78_R16_0_I0 /\ Inv70_1e2e_R6_3_I1 /\ HandleRequestVoteRequestAction => Inv70_1e2e_R6_3_I1' BY DEF TypeOK,Inv5_9e78_R16_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv70_1e2e_R6_3_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv70_1e2e_R6_3_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv70_1e2e_R6_3_I1 /\ HandleRequestVoteResponseAction => Inv70_1e2e_R6_3_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv70_1e2e_R6_3_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv70_1e2e_R6_3_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv70_1e2e_R6_3_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv70_1e2e_R6_3_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv70_1e2e_R6_3_I1
  \* (Inv70_1e2e_R6_3_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv70_1e2e_R6_3_I1 /\ HandleAppendEntriesResponseAction => Inv70_1e2e_R6_3_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv70_1e2e_R6_3_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv5_9e78_R16_0_I0
THEOREM L_28 == TypeOK /\ Inv5_9e78_R16_0_I0 /\ Next => Inv5_9e78_R16_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv5_9e78_R16_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv5_9e78_R16_0_I0 /\ RequestVoteAction => Inv5_9e78_R16_0_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv5_9e78_R16_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5_9e78_R16_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv5_9e78_R16_0_I0 /\ UpdateTermAction => Inv5_9e78_R16_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv5_9e78_R16_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5_9e78_R16_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv5_9e78_R16_0_I0 /\ BecomeLeaderAction => Inv5_9e78_R16_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv5_9e78_R16_0_I0
  \* (Inv5_9e78_R16_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv5_9e78_R16_0_I0 /\ ClientRequestAction => Inv5_9e78_R16_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv5_9e78_R16_0_I0
  \* (Inv5_9e78_R16_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv5_9e78_R16_0_I0 /\ AppendEntriesAction => Inv5_9e78_R16_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv5_9e78_R16_0_I0
  \* (Inv5_9e78_R16_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv5_9e78_R16_0_I0 /\ HandleRequestVoteRequestAction => Inv5_9e78_R16_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_9e78_R16_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5_9e78_R16_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv5_9e78_R16_0_I0 /\ HandleRequestVoteResponseAction => Inv5_9e78_R16_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv5_9e78_R16_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5_9e78_R16_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv5_9e78_R16_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv5_9e78_R16_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv5_9e78_R16_0_I0
  \* (Inv5_9e78_R16_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv5_9e78_R16_0_I0 /\ HandleAppendEntriesResponseAction => Inv5_9e78_R16_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv5_9e78_R16_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv109_4308_R6_1_I1
THEOREM L_29 == TypeOK /\ Inv13_c904_R12_0_I0 /\ Inv109_4308_R6_1_I1 /\ Next => Inv109_4308_R6_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv109_4308_R6_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv109_4308_R6_1_I1 /\ RequestVoteAction => Inv109_4308_R6_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv109_4308_R6_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv109_4308_R6_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv109_4308_R6_1_I1 /\ UpdateTermAction => Inv109_4308_R6_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv109_4308_R6_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv109_4308_R6_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv109_4308_R6_1_I1 /\ BecomeLeaderAction => Inv109_4308_R6_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv109_4308_R6_1_I1
  \* (Inv109_4308_R6_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv109_4308_R6_1_I1 /\ ClientRequestAction => Inv109_4308_R6_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv109_4308_R6_1_I1
  \* (Inv109_4308_R6_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv109_4308_R6_1_I1 /\ AppendEntriesAction => Inv109_4308_R6_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv109_4308_R6_1_I1
  \* (Inv109_4308_R6_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv109_4308_R6_1_I1 /\ HandleRequestVoteRequestAction => Inv109_4308_R6_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv109_4308_R6_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv109_4308_R6_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv109_4308_R6_1_I1 /\ HandleRequestVoteResponseAction => Inv109_4308_R6_1_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv109_4308_R6_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv109_4308_R6_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv13_c904_R12_0_I0 /\ Inv109_4308_R6_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv109_4308_R6_1_I1' BY DEF TypeOK,Inv13_c904_R12_0_I0,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv109_4308_R6_1_I1
  \* (Inv109_4308_R6_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv109_4308_R6_1_I1 /\ HandleAppendEntriesResponseAction => Inv109_4308_R6_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv109_4308_R6_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv672_4aa6_R6_2_I1
THEOREM L_30 == TypeOK /\ Inv1082_1f30_R6_2_I1 /\ Inv672_4aa6_R6_2_I1 /\ Next => Inv672_4aa6_R6_2_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv672_4aa6_R6_2_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv1082_1f30_R6_2_I1 /\ Inv672_4aa6_R6_2_I1 /\ RequestVoteAction => Inv672_4aa6_R6_2_I1' BY DEF TypeOK,Inv1082_1f30_R6_2_I1,RequestVoteAction,RequestVote,Inv672_4aa6_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv672_4aa6_R6_2_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv672_4aa6_R6_2_I1 /\ UpdateTermAction => Inv672_4aa6_R6_2_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv672_4aa6_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv672_4aa6_R6_2_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv672_4aa6_R6_2_I1 /\ BecomeLeaderAction => Inv672_4aa6_R6_2_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv672_4aa6_R6_2_I1
  \* (Inv672_4aa6_R6_2_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv672_4aa6_R6_2_I1 /\ ClientRequestAction => Inv672_4aa6_R6_2_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv672_4aa6_R6_2_I1
  \* (Inv672_4aa6_R6_2_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv672_4aa6_R6_2_I1 /\ AppendEntriesAction => Inv672_4aa6_R6_2_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv672_4aa6_R6_2_I1
  \* (Inv672_4aa6_R6_2_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv672_4aa6_R6_2_I1 /\ HandleRequestVoteRequestAction => Inv672_4aa6_R6_2_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv672_4aa6_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv672_4aa6_R6_2_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv672_4aa6_R6_2_I1 /\ HandleRequestVoteResponseAction => Inv672_4aa6_R6_2_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv672_4aa6_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv672_4aa6_R6_2_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv672_4aa6_R6_2_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv672_4aa6_R6_2_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv672_4aa6_R6_2_I1
  \* (Inv672_4aa6_R6_2_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv672_4aa6_R6_2_I1 /\ HandleAppendEntriesResponseAction => Inv672_4aa6_R6_2_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv672_4aa6_R6_2_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv4_c57a_R6_2_I1
THEOREM L_31 == TypeOK /\ Inv8_441b_R14_1_I1 /\ Inv42_3acc_R5_1_I1 /\ Inv0_e30e_R11_0_I1 /\ Inv0_2c32_R8_1_I1 /\ Inv8407_edca_R14_2_I2 /\ Inv9_f533_R11_1_I0 /\ Inv8_2014_R14_0_I1 /\ Inv0_33b0_R0_0_I0 /\ Inv4_c57a_R6_2_I1 /\ Next => Inv4_c57a_R6_2_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv4_c57a_R6_2_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv4_c57a_R6_2_I1 /\ RequestVoteAction => Inv4_c57a_R6_2_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv4_c57a_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv4_c57a_R6_2_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv4_c57a_R6_2_I1 /\ UpdateTermAction => Inv4_c57a_R6_2_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv4_c57a_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv4_c57a_R6_2_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv4_c57a_R6_2_I1 /\ BecomeLeaderAction => Inv4_c57a_R6_2_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv4_c57a_R6_2_I1
  \* (Inv4_c57a_R6_2_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv8_441b_R14_1_I1 /\ Inv42_3acc_R5_1_I1 /\ Inv0_e30e_R11_0_I1 /\ Inv0_2c32_R8_1_I1 /\ Inv4_c57a_R6_2_I1 /\ ClientRequestAction => Inv4_c57a_R6_2_I1' BY DEF TypeOK,Inv8_441b_R14_1_I1,Inv42_3acc_R5_1_I1,Inv0_e30e_R11_0_I1,Inv0_2c32_R8_1_I1,ClientRequestAction,ClientRequest,Inv4_c57a_R6_2_I1
  \* (Inv4_c57a_R6_2_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv4_c57a_R6_2_I1 /\ AppendEntriesAction => Inv4_c57a_R6_2_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv4_c57a_R6_2_I1
  \* (Inv4_c57a_R6_2_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv4_c57a_R6_2_I1 /\ HandleRequestVoteRequestAction => Inv4_c57a_R6_2_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv4_c57a_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv4_c57a_R6_2_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv8407_edca_R14_2_I2 /\ Inv9_f533_R11_1_I0 /\ Inv4_c57a_R6_2_I1 /\ HandleRequestVoteResponseAction => Inv4_c57a_R6_2_I1' BY DEF TypeOK,Inv8407_edca_R14_2_I2,Inv9_f533_R11_1_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv4_c57a_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv4_c57a_R6_2_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv8_2014_R14_0_I1 /\ Inv0_33b0_R0_0_I0 /\ Inv4_c57a_R6_2_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv4_c57a_R6_2_I1' BY DEF TypeOK,Inv8_2014_R14_0_I1,Inv0_33b0_R0_0_I0,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv4_c57a_R6_2_I1
  \* (Inv4_c57a_R6_2_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv4_c57a_R6_2_I1 /\ HandleAppendEntriesResponseAction => Inv4_c57a_R6_2_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv4_c57a_R6_2_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv8_2014_R14_0_I1
THEOREM L_32 == TypeOK /\ Inv18_0a54_R24_0_I0 /\ Inv1082_1f30_R6_2_I1 /\ Inv12_afc0_R24_0_I0 /\ Inv8_441b_R14_1_I1 /\ Inv8_2014_R14_0_I1 /\ Next => Inv8_2014_R14_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv8_2014_R14_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv8_2014_R14_0_I1 /\ RequestVoteAction => Inv8_2014_R14_0_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv8_2014_R14_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv8_2014_R14_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv8_2014_R14_0_I1 /\ UpdateTermAction => Inv8_2014_R14_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv8_2014_R14_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv8_2014_R14_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv8_2014_R14_0_I1 /\ BecomeLeaderAction => Inv8_2014_R14_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv8_2014_R14_0_I1
  \* (Inv8_2014_R14_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv8_2014_R14_0_I1 /\ ClientRequestAction => Inv8_2014_R14_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv8_2014_R14_0_I1
  \* (Inv8_2014_R14_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv18_0a54_R24_0_I0 /\ Inv1082_1f30_R6_2_I1 /\ Inv12_afc0_R24_0_I0 /\ Inv8_441b_R14_1_I1 /\ Inv8_2014_R14_0_I1 /\ AppendEntriesAction => Inv8_2014_R14_0_I1' BY DEF TypeOK,Inv18_0a54_R24_0_I0,Inv1082_1f30_R6_2_I1,Inv12_afc0_R24_0_I0,Inv8_441b_R14_1_I1,AppendEntriesAction,AppendEntries,Inv8_2014_R14_0_I1
  \* (Inv8_2014_R14_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv8_2014_R14_0_I1 /\ HandleRequestVoteRequestAction => Inv8_2014_R14_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv8_2014_R14_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv8_2014_R14_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv8_2014_R14_0_I1 /\ HandleRequestVoteResponseAction => Inv8_2014_R14_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv8_2014_R14_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv8_2014_R14_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv8_2014_R14_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv8_2014_R14_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv8_2014_R14_0_I1
  \* (Inv8_2014_R14_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv8_2014_R14_0_I1 /\ HandleAppendEntriesResponseAction => Inv8_2014_R14_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv8_2014_R14_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv18_0a54_R24_0_I0
THEOREM L_33 == TypeOK /\ Inv18_0a54_R24_0_I0 /\ Next => Inv18_0a54_R24_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv18_0a54_R24_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv18_0a54_R24_0_I0 /\ RequestVoteAction => Inv18_0a54_R24_0_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv18_0a54_R24_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv18_0a54_R24_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv18_0a54_R24_0_I0 /\ UpdateTermAction => Inv18_0a54_R24_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv18_0a54_R24_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv18_0a54_R24_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv18_0a54_R24_0_I0 /\ BecomeLeaderAction => Inv18_0a54_R24_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv18_0a54_R24_0_I0
  \* (Inv18_0a54_R24_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv18_0a54_R24_0_I0 /\ ClientRequestAction => Inv18_0a54_R24_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv18_0a54_R24_0_I0
  \* (Inv18_0a54_R24_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv18_0a54_R24_0_I0 /\ AppendEntriesAction => Inv18_0a54_R24_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv18_0a54_R24_0_I0
  \* (Inv18_0a54_R24_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv18_0a54_R24_0_I0 /\ HandleRequestVoteRequestAction => Inv18_0a54_R24_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv18_0a54_R24_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv18_0a54_R24_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv18_0a54_R24_0_I0 /\ HandleRequestVoteResponseAction => Inv18_0a54_R24_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv18_0a54_R24_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv18_0a54_R24_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv18_0a54_R24_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv18_0a54_R24_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv18_0a54_R24_0_I0
  \* (Inv18_0a54_R24_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv18_0a54_R24_0_I0 /\ HandleAppendEntriesResponseAction => Inv18_0a54_R24_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv18_0a54_R24_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv12_afc0_R24_0_I0
THEOREM L_34 == TypeOK /\ Inv13_c904_R12_0_I0 /\ Inv12_afc0_R24_0_I0 /\ Next => Inv12_afc0_R24_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv12_afc0_R24_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv12_afc0_R24_0_I0 /\ RequestVoteAction => Inv12_afc0_R24_0_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv12_afc0_R24_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv12_afc0_R24_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv12_afc0_R24_0_I0 /\ UpdateTermAction => Inv12_afc0_R24_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv12_afc0_R24_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv12_afc0_R24_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv12_afc0_R24_0_I0 /\ BecomeLeaderAction => Inv12_afc0_R24_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv12_afc0_R24_0_I0
  \* (Inv12_afc0_R24_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv12_afc0_R24_0_I0 /\ ClientRequestAction => Inv12_afc0_R24_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv12_afc0_R24_0_I0
  \* (Inv12_afc0_R24_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv12_afc0_R24_0_I0 /\ AppendEntriesAction => Inv12_afc0_R24_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv12_afc0_R24_0_I0
  \* (Inv12_afc0_R24_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv12_afc0_R24_0_I0 /\ HandleRequestVoteRequestAction => Inv12_afc0_R24_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv12_afc0_R24_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv12_afc0_R24_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv12_afc0_R24_0_I0 /\ HandleRequestVoteResponseAction => Inv12_afc0_R24_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv12_afc0_R24_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv12_afc0_R24_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv13_c904_R12_0_I0 /\ Inv12_afc0_R24_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv12_afc0_R24_0_I0' BY DEF TypeOK,Inv13_c904_R12_0_I0,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv12_afc0_R24_0_I0
  \* (Inv12_afc0_R24_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv12_afc0_R24_0_I0 /\ HandleAppendEntriesResponseAction => Inv12_afc0_R24_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv12_afc0_R24_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv8407_edca_R14_2_I2
THEOREM L_35 == TypeOK /\ Inv9_f533_R11_1_I0 /\ Inv10_3715_R21_0_I0 /\ Inv9_f533_R11_1_I0 /\ Inv10_3715_R21_0_I0 /\ Inv8407_edca_R14_2_I2 /\ Next => Inv8407_edca_R14_2_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv8407_edca_R14_2_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv9_f533_R11_1_I0 /\ Inv10_3715_R21_0_I0 /\ Inv8407_edca_R14_2_I2 /\ RequestVoteAction => Inv8407_edca_R14_2_I2' BY DEF TypeOK,Inv9_f533_R11_1_I0,Inv10_3715_R21_0_I0,RequestVoteAction,RequestVote,Inv8407_edca_R14_2_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv8407_edca_R14_2_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv9_f533_R11_1_I0 /\ Inv10_3715_R21_0_I0 /\ Inv8407_edca_R14_2_I2 /\ UpdateTermAction => Inv8407_edca_R14_2_I2' BY DEF TypeOK,Inv9_f533_R11_1_I0,Inv10_3715_R21_0_I0,UpdateTermAction,UpdateTerm,Inv8407_edca_R14_2_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv8407_edca_R14_2_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv8407_edca_R14_2_I2 /\ BecomeLeaderAction => Inv8407_edca_R14_2_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv8407_edca_R14_2_I2
  \* (Inv8407_edca_R14_2_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv8407_edca_R14_2_I2 /\ ClientRequestAction => Inv8407_edca_R14_2_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv8407_edca_R14_2_I2
  \* (Inv8407_edca_R14_2_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv8407_edca_R14_2_I2 /\ AppendEntriesAction => Inv8407_edca_R14_2_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv8407_edca_R14_2_I2
  \* (Inv8407_edca_R14_2_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv8407_edca_R14_2_I2 /\ HandleRequestVoteRequestAction => Inv8407_edca_R14_2_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv8407_edca_R14_2_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv8407_edca_R14_2_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv8407_edca_R14_2_I2 /\ HandleRequestVoteResponseAction => Inv8407_edca_R14_2_I2' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv8407_edca_R14_2_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv8407_edca_R14_2_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv8407_edca_R14_2_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv8407_edca_R14_2_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv8407_edca_R14_2_I2
  \* (Inv8407_edca_R14_2_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv8407_edca_R14_2_I2 /\ HandleAppendEntriesResponseAction => Inv8407_edca_R14_2_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv8407_edca_R14_2_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv7_7bad_R0_2_I0
THEOREM L_36 == TypeOK /\ Inv15883_404d_R2_1_I2 /\ Inv7_7bad_R0_2_I0 /\ Next => Inv7_7bad_R0_2_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv7_7bad_R0_2_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv7_7bad_R0_2_I0 /\ RequestVoteAction => Inv7_7bad_R0_2_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv7_7bad_R0_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7_7bad_R0_2_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv7_7bad_R0_2_I0 /\ UpdateTermAction => Inv7_7bad_R0_2_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv7_7bad_R0_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7_7bad_R0_2_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv15883_404d_R2_1_I2 /\ Inv7_7bad_R0_2_I0 /\ BecomeLeaderAction => Inv7_7bad_R0_2_I0' BY DEF TypeOK,Inv15883_404d_R2_1_I2,BecomeLeaderAction,BecomeLeader,Inv7_7bad_R0_2_I0
  \* (Inv7_7bad_R0_2_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv7_7bad_R0_2_I0 /\ ClientRequestAction => Inv7_7bad_R0_2_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv7_7bad_R0_2_I0
  \* (Inv7_7bad_R0_2_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv7_7bad_R0_2_I0 /\ AppendEntriesAction => Inv7_7bad_R0_2_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv7_7bad_R0_2_I0
  \* (Inv7_7bad_R0_2_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv7_7bad_R0_2_I0 /\ HandleRequestVoteRequestAction => Inv7_7bad_R0_2_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7_7bad_R0_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7_7bad_R0_2_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv7_7bad_R0_2_I0 /\ HandleRequestVoteResponseAction => Inv7_7bad_R0_2_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv7_7bad_R0_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7_7bad_R0_2_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv7_7bad_R0_2_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv7_7bad_R0_2_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv7_7bad_R0_2_I0
  \* (Inv7_7bad_R0_2_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv7_7bad_R0_2_I0 /\ HandleAppendEntriesResponseAction => Inv7_7bad_R0_2_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv7_7bad_R0_2_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv9_82b3_R10_1_I0
THEOREM L_37 == TypeOK /\ Inv10_3715_R21_0_I0 /\ Inv9_82b3_R10_1_I0 /\ Next => Inv9_82b3_R10_1_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv9_82b3_R10_1_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv9_82b3_R10_1_I0 /\ RequestVoteAction => Inv9_82b3_R10_1_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv9_82b3_R10_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv9_82b3_R10_1_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv9_82b3_R10_1_I0 /\ UpdateTermAction => Inv9_82b3_R10_1_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv9_82b3_R10_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv9_82b3_R10_1_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv9_82b3_R10_1_I0 /\ BecomeLeaderAction => Inv9_82b3_R10_1_I0' BY DEF TypeOK,Inv15883_404d_R2_1_I2,BecomeLeaderAction,BecomeLeader,Inv9_82b3_R10_1_I0
  \* (Inv9_82b3_R10_1_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv9_82b3_R10_1_I0 /\ ClientRequestAction => Inv9_82b3_R10_1_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv9_82b3_R10_1_I0
  \* (Inv9_82b3_R10_1_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv9_82b3_R10_1_I0 /\ AppendEntriesAction => Inv9_82b3_R10_1_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv9_82b3_R10_1_I0
  \* (Inv9_82b3_R10_1_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv10_3715_R21_0_I0 /\ Inv9_82b3_R10_1_I0 /\ HandleRequestVoteRequestAction => Inv9_82b3_R10_1_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv10_3715_R21_0_I0,
                        Inv9_82b3_R10_1_I0,
                        NEW m \in requestVoteRequestMsgs,
                        HandleRequestVoteRequest(m),
                        NEW mi \in requestVoteResponseMsgs', NEW mj \in requestVoteResponseMsgs',
                        (/\ mi.mterm = mj.mterm /\ mi.msource = mj.msource /\ mi.mvoteGranted /\ mj.mvoteGranted)'
                 PROVE  (mi.mdest = mj.mdest)'
      BY DEF HandleRequestVoteRequestAction, Inv9_82b3_R10_1_I0
    <2>1. CASE m.mterm # currentTerm[m.mdest]
          BY <2>1 DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R10_1_I0,Inv10_3715_R21_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>2. CASE m.mterm = currentTerm[m.mdest] /\ votedFor[m.mdest] \notin {Nil, m.msource}
              BY <2>2 DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R10_1_I0,Inv10_3715_R21_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>3. CASE m.mterm = currentTerm[m.mdest] /\ votedFor[m.mdest] \in {Nil, m.msource}
        <3>1. CASE m.mdest # mi.msource
            BY <2>3,<3>1 DEF TypeOK,Inv10_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R10_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         \* m is the vote request message so its dest is the one receivign the vote request.         
         <3>2. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] # mi.mterm
                BY <2>3,<3>2 DEF TypeOK,Inv10_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R10_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>3. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest # mi.msource
                BY <2>3,<3>3 DEF TypeOK,Inv10_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R10_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>4. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest = mi.msource /\ mi \in requestVoteResponseMsgs
            <4>1. currentTerm[mi.msource] = mi.mterm /\ mi.mvoteGranted
                BY <2>3,<3>4 DEF TypeOK,Inv10_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R10_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>2. votedFor[mi.msource] = mi.mdest
                BY <4>1, <2>3,<3>4 DEF TypeOK,Inv10_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R10_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. QED 
                BY <4>1, <4>2,<3>4,<2>3 DEF TypeOK,Inv10_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R10_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>5. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest = mi.msource /\ mi \notin requestVoteResponseMsgs /\ mj \notin requestVoteResponseMsgs
            <4>1. currentTerm[mi.msource] = mi.mterm /\ mi.mvoteGranted
                BY <2>3,<3>5 DEF TypeOK,Inv10_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R10_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. QED BY <4>1, <2>3,<3>5 DEF TypeOK,Inv10_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R10_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>6. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ ~mi.mvoteGranted /\ m.mdest = mi.msource /\ mi \notin requestVoteResponseMsgs /\ mj \in requestVoteResponseMsgs
            <4>2. votedFor[m.mdest] = mi.mdest
                BY <2>3,<3>6 DEF TypeOK,Inv10_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R10_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            
            <4>3. QED BY <2>3,<3>6 DEF TypeOK,Inv10_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R10_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>7. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ mi.mvoteGranted 
                                         /\ mj.mvoteGranted /\ m.mdest = mi.msource 
                                         /\ mi \notin requestVoteResponseMsgs /\ mj \in requestVoteResponseMsgs
                                         /\ votedFor[m.mdest] = Nil
            <4>2. votedFor'[m.mdest] = mi.mdest
                BY <2>3,<3>7 DEF TypeOK,Inv10_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R10_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. votedFor'[m.mdest] = mj.mdest
                BY SMTT(30),<2>3,<3>7 DEF TypeOK,Inv10_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R10_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero            
            <4>4. QED BY <4>2, <4>3, <2>3,<3>7 DEF TypeOK,Inv10_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R10_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>8. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ mi.mvoteGranted 
                                         /\ mj.mvoteGranted /\ m.mdest = mi.msource 
                                         /\ mi \notin requestVoteResponseMsgs /\ mj \in requestVoteResponseMsgs
                                         /\ votedFor[m.mdest] = m.msource
            <4>2. votedFor'[m.mdest] = mi.mdest
                BY <2>3,<3>8 DEF TypeOK,Inv10_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R10_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. votedFor'[m.mdest] = m.msource
                BY <2>3,<3>8 DEF TypeOK,Inv10_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R10_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>4. mi.mdest = m.msource
                BY <2>3,<3>8 DEF TypeOK,Inv10_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R10_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>5. currentTerm[mj.msource] = mj.mterm
                BY <2>3,<3>8 DEF TypeOK,Inv10_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R10_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>6. votedFor[mj.msource] = mj.mdest
              BY <2>3,<3>8, <4>5 DEF TypeOK,Inv10_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R10_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            
            <4>7. QED BY <4>2, <4>3, <4>4,<4>6, <2>3,<3>8 
            DEF TypeOK,Inv10_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R10_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
                                            
         <3>. QED BY <3>1, <3>2, <3>3,<3>4,<3>5,<3>6,<3>7,<3>8
                     DEF TypeOK,Inv10_3715_R21_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_82b3_R10_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         
    <2> QED
      BY <2>1, <2>2, <2>3 DEF TypeOK,Inv9_82b3_R10_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_3715_R21_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
      ,TypeOK,Inv9_82b3_R10_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_3715_R21_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv9_82b3_R10_1_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv9_82b3_R10_1_I0 /\ HandleRequestVoteResponseAction => Inv9_82b3_R10_1_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv9_82b3_R10_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv9_82b3_R10_1_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv9_82b3_R10_1_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv9_82b3_R10_1_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv9_82b3_R10_1_I0
  \* (Inv9_82b3_R10_1_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv9_82b3_R10_1_I0 /\ HandleAppendEntriesResponseAction => Inv9_82b3_R10_1_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv9_82b3_R10_1_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0,A1,A2,A3,A4,A5,A6,A7
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal
    <1>2. Init => Inv0_33b0_R0_0_I0 BY DEF Init, Inv0_33b0_R0_0_I0, IndGlobal
    <1>3. Init => Inv21336_7e0d_R1_1_I2 BY DEF Init, Inv21336_7e0d_R1_1_I2, IndGlobal
    <1>4. Init => Inv17_ed8d_R0_1_I0 BY DEF Init, Inv17_ed8d_R0_1_I0, IndGlobal
    <1>5. Init => Inv15883_404d_R2_1_I2 BY DEF Init, Inv15883_404d_R2_1_I2, IndGlobal
    <1>6. Init => Inv4_8e53_R5_0_I0 BY DEF Init, Inv4_8e53_R5_0_I0, IndGlobal
    <1>7. Init => Inv6_42ac_R5_1_I1 BY DEF Init, Inv6_42ac_R5_1_I1, IndGlobal
    <1>8. Init => Inv0_e30e_R11_0_I1 BY DEF Init, Inv0_e30e_R11_0_I1, IndGlobal
    <1>9. Init => Inv10_3715_R21_0_I0 BY DEF Init, Inv10_3715_R21_0_I0, IndGlobal
    <1>10. Init => Inv9_f533_R11_1_I0 BY DEF Init, Inv9_f533_R11_1_I0, IndGlobal
    <1>11. Init => Inv0_2c32_R8_1_I1 BY DEF Init, Inv0_2c32_R8_1_I1, IndGlobal
    <1>12. Init => Inv10_928b_R5_1_I1 BY DEF Init, Inv10_928b_R5_1_I1, IndGlobal
    <1>13. Init => Inv877_09bb_R9_0_I1 BY DEF Init, Inv877_09bb_R9_0_I1, IndGlobal
    <1>14. Init => Inv480_fe26_R17_0_I1 BY DEF Init, Inv480_fe26_R17_0_I1, IndGlobal
    <1>15. Init => Inv42_3acc_R5_1_I1 BY DEF Init, Inv42_3acc_R5_1_I1, IndGlobal
    <1>16. Init => Inv28_5a2e_R2_2_I0 BY DEF Init, Inv28_5a2e_R2_2_I0, IndGlobal
    <1>17. Init => Inv22504_7f3f_R4_1_I2 BY DEF Init, Inv22504_7f3f_R4_1_I2, IndGlobal
    <1>18. Init => Inv7027_6cb8_R7_1_I2 BY DEF Init, Inv7027_6cb8_R7_1_I2, IndGlobal
    <1>19. Init => Inv1082_1f30_R6_2_I1 BY DEF Init, Inv1082_1f30_R6_2_I1, IndGlobal
    <1>20. Init => Inv40_2a9c_R7_1_I2 BY DEF Init, Inv40_2a9c_R7_1_I2, IndGlobal
    <1>21. Init => Inv1152_5d57_R18_0_I1 BY DEF Init, Inv1152_5d57_R18_0_I1, IndGlobal
    <1>22. Init => Inv13_c904_R12_0_I0 BY DEF Init, Inv13_c904_R12_0_I0, IndGlobal
    <1>23. Init => Inv21_a5e5_R23_0_I0 BY DEF Init, Inv21_a5e5_R23_0_I0, IndGlobal
    <1>24. Init => Inv8_441b_R14_1_I1 BY DEF Init, Inv8_441b_R14_1_I1, IndGlobal
    <1>25. Init => Inv6346_3776_R25_0_I2 BY DEF Init, Inv6346_3776_R25_0_I2, IndGlobal
    <1>26. Init => Inv2_12a2_R34_1_I1 BY DEF Init, Inv2_12a2_R34_1_I1, IndGlobal
    <1>27. Init => Inv70_1e2e_R6_3_I1 BY DEF Init, Inv70_1e2e_R6_3_I1, IndGlobal
    <1>28. Init => Inv5_9e78_R16_0_I0 BY DEF Init, Inv5_9e78_R16_0_I0, IndGlobal
    <1>29. Init => Inv109_4308_R6_1_I1 BY DEF Init, Inv109_4308_R6_1_I1, IndGlobal
    <1>30. Init => Inv672_4aa6_R6_2_I1 BY DEF Init, Inv672_4aa6_R6_2_I1, IndGlobal
    <1>31. Init => Inv4_c57a_R6_2_I1 BY DEF Init, Inv4_c57a_R6_2_I1, IndGlobal
    <1>32. Init => Inv8_2014_R14_0_I1 BY DEF Init, Inv8_2014_R14_0_I1, IndGlobal
    <1>33. Init => Inv18_0a54_R24_0_I0 BY DEF Init, Inv18_0a54_R24_0_I0, IndGlobal
    <1>34. Init => Inv12_afc0_R24_0_I0 BY DEF Init, Inv12_afc0_R24_0_I0, IndGlobal
    <1>35. Init => Inv8407_edca_R14_2_I2 BY DEF Init, Inv8407_edca_R14_2_I2, IndGlobal
    <1>36. Init => Inv7_7bad_R0_2_I0 BY DEF Init, Inv7_7bad_R0_2_I0, IndGlobal
    <1>37. Init => Inv9_82b3_R10_1_I0 BY DEF Init, Inv9_82b3_R10_1_I0, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14,<1>15,<1>16,<1>17,<1>18,<1>19,<1>20,<1>21,<1>22,<1>23,<1>24,<1>25,<1>26,<1>27,<1>28,<1>29,<1>30,<1>31,<1>32,<1>33,<1>34,<1>35,<1>36,<1>37 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13,L_14,L_15,L_16,L_17,L_18,L_19,L_20,L_21,L_22,L_23,L_24,L_25,L_26,L_27,L_28,L_29,L_30,L_31,L_32,L_33,L_34,L_35,L_36,L_37 DEF Next, IndGlobal

====
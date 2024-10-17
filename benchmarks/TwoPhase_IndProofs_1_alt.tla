---- MODULE TwoPhase_IndProofs_1_alt ----
EXTENDS TwoPhase,TLAPS

\* Proof Graph Stats
\* ==================
\* seed: 1
\* num proof graph nodes: 10
\* num proof obligations: 70
Safety == H_TCConsistent
Inv1_3ca6_R0_0_I0 == \A VARRMI \in RM : (([type |-> "Prepared", rm |-> VARRMI] \in msgsPrepared) \/ (~(tmPrepared = tmPrepared \cup {VARRMI})))
Inv8_8a08_R0_0_I0 == \A VARRMI \in RM : (~([type |-> "Prepared", rm |-> VARRMI] \in msgsPrepared) \/ (~(rmState[VARRMI] = "working")))
Inv3_6839_R0_0_I0 == ((tmPrepared = RM) \/ (~([type |-> "Commit"] \in msgsCommit)))
Inv0_3e99_R0_0_I0 == \A VARRMI \in RM : (([type |-> "Commit"] \in msgsCommit) \/ (~(rmState[VARRMI] = "committed")))
Inv4_abe1_R0_1_I0 == (~([type |-> "Abort"] \in msgsAbort) \/ (~([type |-> "Commit"] \in msgsCommit)))
Inv6_4a91_R0_2_I0 == \A VARRMI \in RM : (~([type |-> "Commit"] \in msgsCommit) \/ (~(rmState[VARRMI] = "aborted")))
Inv7_9687_R5_0_I0 == (~([type |-> "Commit"] \in msgsCommit) \/ (~(tmState = "init")))
Inv5_b7fb_R5_1_I0 == (~([type |-> "Abort"] \in msgsAbort) \/ (~(tmState = "init")))
Inv2_374f_R6_2_I0 == \A VARRMI \in RM : ((rmState[VARRMI] = "prepared") \/ (~([type |-> "Prepared", rm |-> VARRMI] \in msgsPrepared) \/ (~(tmState = "init"))))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv1_3ca6_R0_0_I0
  /\ Inv8_8a08_R0_0_I0
  /\ Inv3_6839_R0_0_I0
  /\ Inv0_3e99_R0_0_I0
  /\ Inv4_abe1_R0_1_I0
  /\ Inv7_9687_R5_0_I0
  /\ Inv5_b7fb_R5_1_I0
  /\ Inv6_4a91_R0_2_I0
  /\ Inv2_374f_R6_2_I0
  
Inv73 == \A VARRMI \in RM : \A VARRMJ \in RM : ~(rmState[VARRMI] = "committed") \/ (~(rmState[VARRMJ] = "working"))
  

THEOREM 
 (/\ Inv1_3ca6_R0_0_I0 
  /\ Inv8_8a08_R0_0_I0
  /\ Inv3_6839_R0_0_I0
  /\ Inv0_3e99_R0_0_I0) => Inv73 
  BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,TypeOK,
  Inv1_3ca6_R0_0_I0,
   Inv8_8a08_R0_0_I0,
   Inv3_6839_R0_0_I0,
   Inv0_3e99_R0_0_I0,
   Inv73 


\* mean in-degree: 1.8
\* median in-degree: 0
\* max in-degree: 8
\* min in-degree: 0
\* mean variable slice size: 0


\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  \* (TypeOK,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ TypeOK /\ RMRcvAbortMsgAction => TypeOK' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,TypeOK
  \* (TypeOK,TMAbortAction)
  <1>2. TypeOK /\ TypeOK /\ TMAbortAction => TypeOK' BY DEF TypeOK,TMAbortAction,TMAbort,TypeOK
  \* (TypeOK,TMCommitAction)
  <1>3. TypeOK /\ TypeOK /\ TMCommitAction => TypeOK' BY DEF TypeOK,TMCommitAction,TMCommit,TypeOK
  \* (TypeOK,TMRcvPreparedAction)
  <1>4. TypeOK /\ TypeOK /\ TMRcvPreparedAction => TypeOK' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,TypeOK
  \* (TypeOK,RMPrepareAction)
  <1>5. TypeOK /\ TypeOK /\ RMPrepareAction => TypeOK' BY DEF TypeOK,RMPrepareAction,RMPrepare,TypeOK
  \* (TypeOK,RMChooseToAbortAction)
  <1>6. TypeOK /\ TypeOK /\ RMChooseToAbortAction => TypeOK' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,TypeOK
  \* (TypeOK,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ TypeOK /\ RMRcvCommitMsgAction => TypeOK' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,TypeOK
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Inv1_3ca6_R0_0_I0 /\ Inv4_abe1_R0_1_I0 /\ Inv0_3e99_R0_0_I0 /\ Inv1_3ca6_R0_0_I0 /\ Inv8_8a08_R0_0_I0 /\ Inv3_6839_R0_0_I0 /\ Inv0_3e99_R0_0_I0 /\ Inv6_4a91_R0_2_I0 /\ Safety /\ Next => Safety'
  \* (Safety,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv1_3ca6_R0_0_I0 /\ Inv4_abe1_R0_1_I0 /\ Inv0_3e99_R0_0_I0 /\ Safety /\ RMRcvAbortMsgAction => Safety' BY DEF TypeOK,Inv1_3ca6_R0_0_I0,Inv4_abe1_R0_1_I0,Inv0_3e99_R0_0_I0,RMRcvAbortMsgAction,RMRcvAbortMsg,Safety,H_TCConsistent
  \* (Safety,TMAbortAction)
  <1>2. TypeOK /\ Safety /\ TMAbortAction => Safety' BY DEF TypeOK,TMAbortAction,TMAbort,Safety,H_TCConsistent
  \* (Safety,TMCommitAction)
  <1>3. TypeOK /\ Safety /\ TMCommitAction => Safety' BY DEF TypeOK,TMCommitAction,TMCommit,Safety,H_TCConsistent
  \* (Safety,TMRcvPreparedAction)
  <1>4. TypeOK /\ Safety /\ TMRcvPreparedAction => Safety' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Safety,H_TCConsistent
  \* (Safety,RMPrepareAction)
  <1>5. TypeOK /\ Safety /\ RMPrepareAction => Safety' BY DEF TypeOK,RMPrepareAction,RMPrepare,Safety,H_TCConsistent
  \* (Safety,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv1_3ca6_R0_0_I0 /\ Inv8_8a08_R0_0_I0 /\ Inv3_6839_R0_0_I0 /\ Inv0_3e99_R0_0_I0 /\ Safety /\ RMChooseToAbortAction => Safety' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv1_3ca6_R0_0_I0,
                        Inv8_8a08_R0_0_I0,
                        Inv0_3e99_R0_0_I0,
                        Safety,
                        TRUE,
                        NEW rm \in RM,
                        RMChooseToAbort(rm),
                        Inv3_6839_R0_0_I0
                 PROVE  Safety'
      BY DEF RMChooseToAbortAction
    <2>1. CASE tmPrepared = RM
      BY <2>1 DEF TypeOK,Inv1_3ca6_R0_0_I0,Inv8_8a08_R0_0_I0,Inv3_6839_R0_0_I0,Inv0_3e99_R0_0_I0,RMChooseToAbortAction,RMChooseToAbort,Safety,H_TCConsistent
    <2>2. CASE ~([type |-> "Commit"] \in msgsCommit)
      BY <2>2 DEF TypeOK,Inv1_3ca6_R0_0_I0,Inv8_8a08_R0_0_I0,Inv3_6839_R0_0_I0,Inv0_3e99_R0_0_I0,RMChooseToAbortAction,RMChooseToAbort,Safety,H_TCConsistent
    <2>3. QED
      BY <2>1, <2>2 DEF Inv3_6839_R0_0_I0
  \* (Safety,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv6_4a91_R0_2_I0 /\ Safety /\ RMRcvCommitMsgAction => Safety' BY DEF TypeOK,Inv6_4a91_R0_2_I0,RMRcvCommitMsgAction,RMRcvCommitMsg,Safety,H_TCConsistent
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv1_3ca6_R0_0_I0
THEOREM L_2 == TypeOK /\ Inv1_3ca6_R0_0_I0 /\ Next => Inv1_3ca6_R0_0_I0'
  \* (Inv1_3ca6_R0_0_I0,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv1_3ca6_R0_0_I0 /\ RMRcvAbortMsgAction => Inv1_3ca6_R0_0_I0' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv1_3ca6_R0_0_I0
  \* (Inv1_3ca6_R0_0_I0,TMAbortAction)
  <1>2. TypeOK /\ Inv1_3ca6_R0_0_I0 /\ TMAbortAction => Inv1_3ca6_R0_0_I0' BY DEF TypeOK,TMAbortAction,TMAbort,Inv1_3ca6_R0_0_I0
  \* (Inv1_3ca6_R0_0_I0,TMCommitAction)
  <1>3. TypeOK /\ Inv1_3ca6_R0_0_I0 /\ TMCommitAction => Inv1_3ca6_R0_0_I0' BY DEF TypeOK,TMCommitAction,TMCommit,Inv1_3ca6_R0_0_I0
  \* (Inv1_3ca6_R0_0_I0,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv1_3ca6_R0_0_I0 /\ TMRcvPreparedAction => Inv1_3ca6_R0_0_I0' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv1_3ca6_R0_0_I0
  \* (Inv1_3ca6_R0_0_I0,RMPrepareAction)
  <1>5. TypeOK /\ Inv1_3ca6_R0_0_I0 /\ RMPrepareAction => Inv1_3ca6_R0_0_I0' BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv1_3ca6_R0_0_I0
  \* (Inv1_3ca6_R0_0_I0,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv1_3ca6_R0_0_I0 /\ RMChooseToAbortAction => Inv1_3ca6_R0_0_I0' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv1_3ca6_R0_0_I0
  \* (Inv1_3ca6_R0_0_I0,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv1_3ca6_R0_0_I0 /\ RMRcvCommitMsgAction => Inv1_3ca6_R0_0_I0' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv1_3ca6_R0_0_I0
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv8_8a08_R0_0_I0
THEOREM L_3 == TypeOK /\ Inv8_8a08_R0_0_I0 /\ Next => Inv8_8a08_R0_0_I0'
  \* (Inv8_8a08_R0_0_I0,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv8_8a08_R0_0_I0 /\ RMRcvAbortMsgAction => Inv8_8a08_R0_0_I0' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv8_8a08_R0_0_I0
  \* (Inv8_8a08_R0_0_I0,TMAbortAction)
  <1>2. TypeOK /\ Inv8_8a08_R0_0_I0 /\ TMAbortAction => Inv8_8a08_R0_0_I0' BY DEF TypeOK,TMAbortAction,TMAbort,Inv8_8a08_R0_0_I0
  \* (Inv8_8a08_R0_0_I0,TMCommitAction)
  <1>3. TypeOK /\ Inv8_8a08_R0_0_I0 /\ TMCommitAction => Inv8_8a08_R0_0_I0' BY DEF TypeOK,TMCommitAction,TMCommit,Inv8_8a08_R0_0_I0
  \* (Inv8_8a08_R0_0_I0,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv8_8a08_R0_0_I0 /\ TMRcvPreparedAction => Inv8_8a08_R0_0_I0' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv8_8a08_R0_0_I0
  \* (Inv8_8a08_R0_0_I0,RMPrepareAction)
  <1>5. TypeOK /\ Inv8_8a08_R0_0_I0 /\ RMPrepareAction => Inv8_8a08_R0_0_I0' BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv8_8a08_R0_0_I0
  \* (Inv8_8a08_R0_0_I0,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv8_8a08_R0_0_I0 /\ RMChooseToAbortAction => Inv8_8a08_R0_0_I0' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv8_8a08_R0_0_I0
  \* (Inv8_8a08_R0_0_I0,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv8_8a08_R0_0_I0 /\ RMRcvCommitMsgAction => Inv8_8a08_R0_0_I0' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv8_8a08_R0_0_I0
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv3_6839_R0_0_I0
THEOREM L_4 == TypeOK /\ Inv3_6839_R0_0_I0 /\ Next => Inv3_6839_R0_0_I0'
  \* (Inv3_6839_R0_0_I0,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv3_6839_R0_0_I0 /\ RMRcvAbortMsgAction => Inv3_6839_R0_0_I0' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv3_6839_R0_0_I0
  \* (Inv3_6839_R0_0_I0,TMAbortAction)
  <1>2. TypeOK /\ Inv3_6839_R0_0_I0 /\ TMAbortAction => Inv3_6839_R0_0_I0' BY DEF TypeOK,TMAbortAction,TMAbort,Inv3_6839_R0_0_I0
  \* (Inv3_6839_R0_0_I0,TMCommitAction)
  <1>3. TypeOK /\ Inv3_6839_R0_0_I0 /\ TMCommitAction => Inv3_6839_R0_0_I0' BY DEF TypeOK,TMCommitAction,TMCommit,Inv3_6839_R0_0_I0
  \* (Inv3_6839_R0_0_I0,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv3_6839_R0_0_I0 /\ TMRcvPreparedAction => Inv3_6839_R0_0_I0' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv3_6839_R0_0_I0
  \* (Inv3_6839_R0_0_I0,RMPrepareAction)
  <1>5. TypeOK /\ Inv3_6839_R0_0_I0 /\ RMPrepareAction => Inv3_6839_R0_0_I0' BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv3_6839_R0_0_I0
  \* (Inv3_6839_R0_0_I0,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv3_6839_R0_0_I0 /\ RMChooseToAbortAction => Inv3_6839_R0_0_I0' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv3_6839_R0_0_I0
  \* (Inv3_6839_R0_0_I0,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv3_6839_R0_0_I0 /\ RMRcvCommitMsgAction => Inv3_6839_R0_0_I0' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv3_6839_R0_0_I0
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv0_3e99_R0_0_I0
THEOREM L_5 == TypeOK /\ Inv0_3e99_R0_0_I0 /\ Next => Inv0_3e99_R0_0_I0'
  \* (Inv0_3e99_R0_0_I0,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv0_3e99_R0_0_I0 /\ RMRcvAbortMsgAction => Inv0_3e99_R0_0_I0' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv0_3e99_R0_0_I0
  \* (Inv0_3e99_R0_0_I0,TMAbortAction)
  <1>2. TypeOK /\ Inv0_3e99_R0_0_I0 /\ TMAbortAction => Inv0_3e99_R0_0_I0' BY DEF TypeOK,TMAbortAction,TMAbort,Inv0_3e99_R0_0_I0
  \* (Inv0_3e99_R0_0_I0,TMCommitAction)
  <1>3. TypeOK /\ Inv0_3e99_R0_0_I0 /\ TMCommitAction => Inv0_3e99_R0_0_I0' BY DEF TypeOK,TMCommitAction,TMCommit,Inv0_3e99_R0_0_I0
  \* (Inv0_3e99_R0_0_I0,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv0_3e99_R0_0_I0 /\ TMRcvPreparedAction => Inv0_3e99_R0_0_I0' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv0_3e99_R0_0_I0
  \* (Inv0_3e99_R0_0_I0,RMPrepareAction)
  <1>5. TypeOK /\ Inv0_3e99_R0_0_I0 /\ RMPrepareAction => Inv0_3e99_R0_0_I0' BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv0_3e99_R0_0_I0
  \* (Inv0_3e99_R0_0_I0,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv0_3e99_R0_0_I0 /\ RMChooseToAbortAction => Inv0_3e99_R0_0_I0' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv0_3e99_R0_0_I0
  \* (Inv0_3e99_R0_0_I0,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv0_3e99_R0_0_I0 /\ RMRcvCommitMsgAction => Inv0_3e99_R0_0_I0' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv0_3e99_R0_0_I0
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv4_abe1_R0_1_I0
THEOREM L_6 == TypeOK /\ Inv7_9687_R5_0_I0 /\ Inv5_b7fb_R5_1_I0 /\ Inv4_abe1_R0_1_I0 /\ Next => Inv4_abe1_R0_1_I0'
  \* (Inv4_abe1_R0_1_I0,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv4_abe1_R0_1_I0 /\ RMRcvAbortMsgAction => Inv4_abe1_R0_1_I0' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv4_abe1_R0_1_I0
  \* (Inv4_abe1_R0_1_I0,TMAbortAction)
  <1>2. TypeOK /\ Inv7_9687_R5_0_I0 /\ Inv4_abe1_R0_1_I0 /\ TMAbortAction => Inv4_abe1_R0_1_I0' BY DEF TypeOK,Inv7_9687_R5_0_I0,TMAbortAction,TMAbort,Inv4_abe1_R0_1_I0
  \* (Inv4_abe1_R0_1_I0,TMCommitAction)
  <1>3. TypeOK /\ Inv5_b7fb_R5_1_I0 /\ Inv4_abe1_R0_1_I0 /\ TMCommitAction => Inv4_abe1_R0_1_I0' BY DEF TypeOK,Inv5_b7fb_R5_1_I0,TMCommitAction,TMCommit,Inv4_abe1_R0_1_I0
  \* (Inv4_abe1_R0_1_I0,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv4_abe1_R0_1_I0 /\ TMRcvPreparedAction => Inv4_abe1_R0_1_I0' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv4_abe1_R0_1_I0
  \* (Inv4_abe1_R0_1_I0,RMPrepareAction)
  <1>5. TypeOK /\ Inv4_abe1_R0_1_I0 /\ RMPrepareAction => Inv4_abe1_R0_1_I0' BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv4_abe1_R0_1_I0
  \* (Inv4_abe1_R0_1_I0,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv4_abe1_R0_1_I0 /\ RMChooseToAbortAction => Inv4_abe1_R0_1_I0' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv4_abe1_R0_1_I0
  \* (Inv4_abe1_R0_1_I0,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv4_abe1_R0_1_I0 /\ RMRcvCommitMsgAction => Inv4_abe1_R0_1_I0' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv4_abe1_R0_1_I0
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv7_9687_R5_0_I0
THEOREM L_7 == TypeOK /\ Inv7_9687_R5_0_I0 /\ Next => Inv7_9687_R5_0_I0'
  \* (Inv7_9687_R5_0_I0,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv7_9687_R5_0_I0 /\ RMRcvAbortMsgAction => Inv7_9687_R5_0_I0' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv7_9687_R5_0_I0
  \* (Inv7_9687_R5_0_I0,TMAbortAction)
  <1>2. TypeOK /\ Inv7_9687_R5_0_I0 /\ TMAbortAction => Inv7_9687_R5_0_I0' BY DEF TypeOK,TMAbortAction,TMAbort,Inv7_9687_R5_0_I0
  \* (Inv7_9687_R5_0_I0,TMCommitAction)
  <1>3. TypeOK /\ Inv7_9687_R5_0_I0 /\ TMCommitAction => Inv7_9687_R5_0_I0' BY DEF TypeOK,TMCommitAction,TMCommit,Inv7_9687_R5_0_I0
  \* (Inv7_9687_R5_0_I0,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv7_9687_R5_0_I0 /\ TMRcvPreparedAction => Inv7_9687_R5_0_I0' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv7_9687_R5_0_I0
  \* (Inv7_9687_R5_0_I0,RMPrepareAction)
  <1>5. TypeOK /\ Inv7_9687_R5_0_I0 /\ RMPrepareAction => Inv7_9687_R5_0_I0' BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv7_9687_R5_0_I0
  \* (Inv7_9687_R5_0_I0,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv7_9687_R5_0_I0 /\ RMChooseToAbortAction => Inv7_9687_R5_0_I0' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv7_9687_R5_0_I0
  \* (Inv7_9687_R5_0_I0,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv7_9687_R5_0_I0 /\ RMRcvCommitMsgAction => Inv7_9687_R5_0_I0' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv7_9687_R5_0_I0
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv5_b7fb_R5_1_I0
THEOREM L_8 == TypeOK /\ Inv5_b7fb_R5_1_I0 /\ Next => Inv5_b7fb_R5_1_I0'
  \* (Inv5_b7fb_R5_1_I0,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv5_b7fb_R5_1_I0 /\ RMRcvAbortMsgAction => Inv5_b7fb_R5_1_I0' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv5_b7fb_R5_1_I0
  \* (Inv5_b7fb_R5_1_I0,TMAbortAction)
  <1>2. TypeOK /\ Inv5_b7fb_R5_1_I0 /\ TMAbortAction => Inv5_b7fb_R5_1_I0' BY DEF TypeOK,TMAbortAction,TMAbort,Inv5_b7fb_R5_1_I0
  \* (Inv5_b7fb_R5_1_I0,TMCommitAction)
  <1>3. TypeOK /\ Inv5_b7fb_R5_1_I0 /\ TMCommitAction => Inv5_b7fb_R5_1_I0' BY DEF TypeOK,TMCommitAction,TMCommit,Inv5_b7fb_R5_1_I0
  \* (Inv5_b7fb_R5_1_I0,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv5_b7fb_R5_1_I0 /\ TMRcvPreparedAction => Inv5_b7fb_R5_1_I0' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv5_b7fb_R5_1_I0
  \* (Inv5_b7fb_R5_1_I0,RMPrepareAction)
  <1>5. TypeOK /\ Inv5_b7fb_R5_1_I0 /\ RMPrepareAction => Inv5_b7fb_R5_1_I0' BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv5_b7fb_R5_1_I0
  \* (Inv5_b7fb_R5_1_I0,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv5_b7fb_R5_1_I0 /\ RMChooseToAbortAction => Inv5_b7fb_R5_1_I0' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv5_b7fb_R5_1_I0
  \* (Inv5_b7fb_R5_1_I0,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv5_b7fb_R5_1_I0 /\ RMRcvCommitMsgAction => Inv5_b7fb_R5_1_I0' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv5_b7fb_R5_1_I0
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv6_4a91_R0_2_I0
THEOREM L_9 == TypeOK /\ Inv4_abe1_R0_1_I0 /\ Inv1_3ca6_R0_0_I0 /\ Inv2_374f_R6_2_I0 /\ Inv3_6839_R0_0_I0 /\ Inv8_8a08_R0_0_I0 /\ Inv1_3ca6_R0_0_I0 /\ Inv6_4a91_R0_2_I0 /\ Next => Inv6_4a91_R0_2_I0'
  \* (Inv6_4a91_R0_2_I0,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv4_abe1_R0_1_I0 /\ Inv6_4a91_R0_2_I0 /\ RMRcvAbortMsgAction => Inv6_4a91_R0_2_I0' BY DEF TypeOK,Inv4_abe1_R0_1_I0,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv6_4a91_R0_2_I0
  \* (Inv6_4a91_R0_2_I0,TMAbortAction)
  <1>2. TypeOK /\ Inv6_4a91_R0_2_I0 /\ TMAbortAction => Inv6_4a91_R0_2_I0' BY DEF TypeOK,TMAbortAction,TMAbort,Inv6_4a91_R0_2_I0
  \* (Inv6_4a91_R0_2_I0,TMCommitAction)
  <1>3. TypeOK /\ Inv1_3ca6_R0_0_I0 /\ Inv2_374f_R6_2_I0 /\ Inv6_4a91_R0_2_I0 /\ TMCommitAction => Inv6_4a91_R0_2_I0' 
    <2> SUFFICES ASSUME TypeOK /\ Inv1_3ca6_R0_0_I0 /\ Inv2_374f_R6_2_I0 /\ Inv6_4a91_R0_2_I0 /\ TMCommitAction,
                        NEW VARRMI \in RM'
                 PROVE  (~([type |-> "Commit"] \in msgsCommit) \/ (~(rmState[VARRMI] = "aborted")))'
      BY DEF Inv6_4a91_R0_2_I0
    <2> QED
      BY DEF TypeOK,Inv1_3ca6_R0_0_I0,Inv2_374f_R6_2_I0,TMCommitAction,TMCommit,Inv6_4a91_R0_2_I0
  \* (Inv6_4a91_R0_2_I0,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv6_4a91_R0_2_I0 /\ TMRcvPreparedAction => Inv6_4a91_R0_2_I0' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv6_4a91_R0_2_I0
  \* (Inv6_4a91_R0_2_I0,RMPrepareAction)
  <1>5. TypeOK /\ Inv6_4a91_R0_2_I0 /\ RMPrepareAction => Inv6_4a91_R0_2_I0' BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv6_4a91_R0_2_I0
  \* (Inv6_4a91_R0_2_I0,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv3_6839_R0_0_I0 /\ Inv8_8a08_R0_0_I0 /\ Inv1_3ca6_R0_0_I0 /\ Inv6_4a91_R0_2_I0 /\ RMChooseToAbortAction => Inv6_4a91_R0_2_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv8_8a08_R0_0_I0,
                        Inv1_3ca6_R0_0_I0,
                        Inv6_4a91_R0_2_I0,
                        TRUE,
                        NEW rm \in RM,
                        RMChooseToAbort(rm),
                        NEW VARRMI \in RM',
                        Inv3_6839_R0_0_I0
                 PROVE  (~([type |-> "Commit"] \in msgsCommit) \/ (~(rmState[VARRMI] = "aborted")))'
      BY DEF Inv6_4a91_R0_2_I0, RMChooseToAbortAction
    <2>1. CASE tmPrepared = RM
      BY <2>1 DEF TypeOK,Inv3_6839_R0_0_I0,Inv8_8a08_R0_0_I0,Inv1_3ca6_R0_0_I0,RMChooseToAbortAction,RMChooseToAbort,Inv6_4a91_R0_2_I0
    <2>2. CASE ~([type |-> "Commit"] \in msgsCommit)
      BY <2>2 DEF TypeOK,Inv3_6839_R0_0_I0,Inv8_8a08_R0_0_I0,Inv1_3ca6_R0_0_I0,RMChooseToAbortAction,RMChooseToAbort,Inv6_4a91_R0_2_I0
    <2>3. QED
      BY <2>1, <2>2 DEF Inv3_6839_R0_0_I0
  \* (Inv6_4a91_R0_2_I0,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv6_4a91_R0_2_I0 /\ RMRcvCommitMsgAction => Inv6_4a91_R0_2_I0' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv6_4a91_R0_2_I0
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv2_374f_R6_2_I0
THEOREM L_10 == TypeOK /\ Inv5_b7fb_R5_1_I0 /\ Inv7_9687_R5_0_I0 /\ Inv2_374f_R6_2_I0 /\ Next => Inv2_374f_R6_2_I0'
  \* (Inv2_374f_R6_2_I0,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv5_b7fb_R5_1_I0 /\ Inv2_374f_R6_2_I0 /\ RMRcvAbortMsgAction => Inv2_374f_R6_2_I0' BY DEF TypeOK,Inv5_b7fb_R5_1_I0,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv2_374f_R6_2_I0
  \* (Inv2_374f_R6_2_I0,TMAbortAction)
  <1>2. TypeOK /\ Inv2_374f_R6_2_I0 /\ TMAbortAction => Inv2_374f_R6_2_I0' BY DEF TypeOK,TMAbortAction,TMAbort,Inv2_374f_R6_2_I0
  \* (Inv2_374f_R6_2_I0,TMCommitAction)
  <1>3. TypeOK /\ Inv2_374f_R6_2_I0 /\ TMCommitAction => Inv2_374f_R6_2_I0' BY DEF TypeOK,TMCommitAction,TMCommit,Inv2_374f_R6_2_I0
  \* (Inv2_374f_R6_2_I0,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv2_374f_R6_2_I0 /\ TMRcvPreparedAction => Inv2_374f_R6_2_I0' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv2_374f_R6_2_I0
  \* (Inv2_374f_R6_2_I0,RMPrepareAction)
  <1>5. TypeOK /\ Inv2_374f_R6_2_I0 /\ RMPrepareAction => Inv2_374f_R6_2_I0' BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv2_374f_R6_2_I0
  \* (Inv2_374f_R6_2_I0,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv2_374f_R6_2_I0 /\ RMChooseToAbortAction => Inv2_374f_R6_2_I0' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv2_374f_R6_2_I0
  \* (Inv2_374f_R6_2_I0,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv7_9687_R5_0_I0 /\ Inv2_374f_R6_2_I0 /\ RMRcvCommitMsgAction => Inv2_374f_R6_2_I0' BY DEF TypeOK,Inv7_9687_R5_0_I0,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv2_374f_R6_2_I0
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal, H_TCConsistent
    <1>2. Init => Inv1_3ca6_R0_0_I0 BY DEF Init, Inv1_3ca6_R0_0_I0, IndGlobal
    <1>3. Init => Inv8_8a08_R0_0_I0 BY DEF Init, Inv8_8a08_R0_0_I0, IndGlobal
    <1>4. Init => Inv3_6839_R0_0_I0 BY DEF Init, Inv3_6839_R0_0_I0, IndGlobal
    <1>5. Init => Inv0_3e99_R0_0_I0 BY DEF Init, Inv0_3e99_R0_0_I0, IndGlobal
    <1>6. Init => Inv4_abe1_R0_1_I0 BY DEF Init, Inv4_abe1_R0_1_I0, IndGlobal
    <1>7. Init => Inv7_9687_R5_0_I0 BY DEF Init, Inv7_9687_R5_0_I0, IndGlobal
    <1>8. Init => Inv5_b7fb_R5_1_I0 BY DEF Init, Inv5_b7fb_R5_1_I0, IndGlobal
    <1>9. Init => Inv6_4a91_R0_2_I0 BY DEF Init, Inv6_4a91_R0_2_I0, IndGlobal
    <1>10. Init => Inv2_374f_R6_2_I0 BY DEF Init, Inv2_374f_R6_2_I0, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10 DEF Next, IndGlobal

====
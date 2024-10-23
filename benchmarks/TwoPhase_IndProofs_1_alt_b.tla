---- MODULE TwoPhase_IndProofs_1_alt_b ----
EXTENDS TwoPhase,TLAPS

\* Proof Graph Stats
\* ==================
\* seed: 1
\* num proof graph nodes: 13
\* num proof obligations: 91
Safety == H_TCConsistent
Inv73_bad3_R0_0_I1 == \A VARRMI \in RM : \A VARRMJ \in RM : ~(rmState[VARRMI] = "committed") \/ (~(rmState[VARRMJ] = "working"))
Inv11_9254_R0_1_I1 == \A VARRMJ \in RM : ~([type |-> "Abort"] \in msgsAbort) \/ (~(rmState[VARRMJ] = "committed"))
Inv23_b2ee_R0_2_I1 == \A VARRMI \in RM : ~([type |-> "Commit"] \in msgsCommit) \/ (~(rmState[VARRMI] = "aborted"))
Inv2_6383_R1_0_I1 == \A VARRMI \in RM : ~([type |-> "Commit"] \in msgsCommit) \/ (~(rmState[VARRMI] = "working"))
Inv1_b34d_R2_0_I1 == ~([type |-> "Abort"] \in msgsAbort) \/ (~([type |-> "Commit"] \in msgsCommit))
Inv53_f69d_R2_1_I1 == \A VARRMI \in RM : ~(rmState[VARRMI] = "committed") \/ (~(tmState = "init"))
Inv1448_1fb0_R3_2_I2 == \A VARRMJ \in RM : (rmState[VARRMJ] = "prepared") \/ (~(tmPrepared = tmPrepared \cup {VARRMJ})) \/ (~(tmState = "init"))
Inv15_48a9_R4_0_I1 == \A VARRMI \in RM : ~(rmState[VARRMI] = "working") \/ (~(tmPrepared = tmPrepared \cup {VARRMI}))
Inv4_98a2_R5_0_I1 == ~([type |-> "Commit"] \in msgsCommit) \/ (~(tmState = "init"))
Inv6_2e0f_R5_1_I1 == ~([type |-> "Abort"] \in msgsAbort) \/ (~(tmState = "init"))
Inv1449_35cb_R7_2_I2 == \A VARRMI \in RM : (rmState[VARRMI] = "prepared") \/ (~([type |-> "Prepared", rm |-> VARRMI] \in msgsPrepared) \/ (~(tmState = "init")))
Inv21_4f76_R8_0_I1 == \A VARRMI \in RM : ~([type |-> "Prepared", rm |-> VARRMI] \in msgsPrepared) \/ (~(rmState[VARRMI] = "working"))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv73_bad3_R0_0_I1
  /\ Inv2_6383_R1_0_I1
  /\ Inv15_48a9_R4_0_I1
  /\ Inv21_4f76_R8_0_I1
  /\ Inv11_9254_R0_1_I1
  /\ Inv1_b34d_R2_0_I1
  /\ Inv4_98a2_R5_0_I1
  /\ Inv6_2e0f_R5_1_I1
  /\ Inv53_f69d_R2_1_I1
  /\ Inv23_b2ee_R0_2_I1
  /\ Inv1448_1fb0_R3_2_I2
  /\ Inv1449_35cb_R7_2_I2


\* mean in-degree: 1.4615384615384615
\* median in-degree: 1
\* max in-degree: 3
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
THEOREM L_1 == TypeOK /\ Inv11_9254_R0_1_I1 /\ Inv73_bad3_R0_0_I1 /\ Inv23_b2ee_R0_2_I1 /\ Safety /\ Next => Safety'
  \* (Safety,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv11_9254_R0_1_I1 /\ Safety /\ RMRcvAbortMsgAction => Safety' BY DEF TypeOK,Inv11_9254_R0_1_I1,RMRcvAbortMsgAction,RMRcvAbortMsg,Safety,H_TCConsistent
  \* (Safety,TMAbortAction)
  <1>2. TypeOK /\ Safety /\ TMAbortAction => Safety' BY DEF TypeOK,TMAbortAction,TMAbort,Safety,H_TCConsistent
  \* (Safety,TMCommitAction)
  <1>3. TypeOK /\ Safety /\ TMCommitAction => Safety' BY DEF TypeOK,TMCommitAction,TMCommit,Safety,H_TCConsistent
  \* (Safety,TMRcvPreparedAction)
  <1>4. TypeOK /\ Safety /\ TMRcvPreparedAction => Safety' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Safety,H_TCConsistent
  \* (Safety,RMPrepareAction)
  <1>5. TypeOK /\ Safety /\ RMPrepareAction => Safety' BY DEF TypeOK,RMPrepareAction,RMPrepare,Safety,H_TCConsistent
  \* (Safety,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv73_bad3_R0_0_I1 /\ Safety /\ RMChooseToAbortAction => Safety' BY DEF TypeOK,Inv73_bad3_R0_0_I1,RMChooseToAbortAction,RMChooseToAbort,Safety,H_TCConsistent
  \* (Safety,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv23_b2ee_R0_2_I1 /\ Safety /\ RMRcvCommitMsgAction => Safety' BY DEF TypeOK,Inv23_b2ee_R0_2_I1,RMRcvCommitMsgAction,RMRcvCommitMsg,Safety,H_TCConsistent
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv73_bad3_R0_0_I1
THEOREM L_2 == TypeOK /\ Inv2_6383_R1_0_I1 /\ Inv73_bad3_R0_0_I1 /\ Next => Inv73_bad3_R0_0_I1'
  \* (Inv73_bad3_R0_0_I1,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv73_bad3_R0_0_I1 /\ RMRcvAbortMsgAction => Inv73_bad3_R0_0_I1' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv73_bad3_R0_0_I1
  \* (Inv73_bad3_R0_0_I1,TMAbortAction)
  <1>2. TypeOK /\ Inv73_bad3_R0_0_I1 /\ TMAbortAction => Inv73_bad3_R0_0_I1' BY DEF TypeOK,TMAbortAction,TMAbort,Inv73_bad3_R0_0_I1
  \* (Inv73_bad3_R0_0_I1,TMCommitAction)
  <1>3. TypeOK /\ Inv73_bad3_R0_0_I1 /\ TMCommitAction => Inv73_bad3_R0_0_I1' BY DEF TypeOK,TMCommitAction,TMCommit,Inv73_bad3_R0_0_I1
  \* (Inv73_bad3_R0_0_I1,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv73_bad3_R0_0_I1 /\ TMRcvPreparedAction => Inv73_bad3_R0_0_I1' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv73_bad3_R0_0_I1
  \* (Inv73_bad3_R0_0_I1,RMPrepareAction)
  <1>5. TypeOK /\ Inv73_bad3_R0_0_I1 /\ RMPrepareAction => Inv73_bad3_R0_0_I1' BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv73_bad3_R0_0_I1
  \* (Inv73_bad3_R0_0_I1,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv73_bad3_R0_0_I1 /\ RMChooseToAbortAction => Inv73_bad3_R0_0_I1' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv73_bad3_R0_0_I1
  \* (Inv73_bad3_R0_0_I1,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv2_6383_R1_0_I1 /\ Inv73_bad3_R0_0_I1 /\ RMRcvCommitMsgAction => Inv73_bad3_R0_0_I1' BY DEF TypeOK,Inv2_6383_R1_0_I1,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv73_bad3_R0_0_I1
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv2_6383_R1_0_I1
THEOREM L_3 == TypeOK /\ Inv15_48a9_R4_0_I1 /\ Inv2_6383_R1_0_I1 /\ Next => Inv2_6383_R1_0_I1'
  \* (Inv2_6383_R1_0_I1,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv2_6383_R1_0_I1 /\ RMRcvAbortMsgAction => Inv2_6383_R1_0_I1' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv2_6383_R1_0_I1
  \* (Inv2_6383_R1_0_I1,TMAbortAction)
  <1>2. TypeOK /\ Inv2_6383_R1_0_I1 /\ TMAbortAction => Inv2_6383_R1_0_I1' BY DEF TypeOK,TMAbortAction,TMAbort,Inv2_6383_R1_0_I1
  \* (Inv2_6383_R1_0_I1,TMCommitAction)
  <1>3. TypeOK /\ Inv15_48a9_R4_0_I1 /\ Inv2_6383_R1_0_I1 /\ TMCommitAction => Inv2_6383_R1_0_I1' BY DEF TypeOK,Inv15_48a9_R4_0_I1,TMCommitAction,TMCommit,Inv2_6383_R1_0_I1
  \* (Inv2_6383_R1_0_I1,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv2_6383_R1_0_I1 /\ TMRcvPreparedAction => Inv2_6383_R1_0_I1' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv2_6383_R1_0_I1
  \* (Inv2_6383_R1_0_I1,RMPrepareAction)
  <1>5. TypeOK /\ Inv2_6383_R1_0_I1 /\ RMPrepareAction => Inv2_6383_R1_0_I1' BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv2_6383_R1_0_I1
  \* (Inv2_6383_R1_0_I1,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv2_6383_R1_0_I1 /\ RMChooseToAbortAction => Inv2_6383_R1_0_I1' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv2_6383_R1_0_I1
  \* (Inv2_6383_R1_0_I1,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv2_6383_R1_0_I1 /\ RMRcvCommitMsgAction => Inv2_6383_R1_0_I1' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv2_6383_R1_0_I1
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv15_48a9_R4_0_I1
THEOREM L_4 == TypeOK /\ Inv21_4f76_R8_0_I1 /\ Inv15_48a9_R4_0_I1 /\ Next => Inv15_48a9_R4_0_I1'
  \* (Inv15_48a9_R4_0_I1,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv15_48a9_R4_0_I1 /\ RMRcvAbortMsgAction => Inv15_48a9_R4_0_I1' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv15_48a9_R4_0_I1
  \* (Inv15_48a9_R4_0_I1,TMAbortAction)
  <1>2. TypeOK /\ Inv15_48a9_R4_0_I1 /\ TMAbortAction => Inv15_48a9_R4_0_I1' BY DEF TypeOK,TMAbortAction,TMAbort,Inv15_48a9_R4_0_I1
  \* (Inv15_48a9_R4_0_I1,TMCommitAction)
  <1>3. TypeOK /\ Inv15_48a9_R4_0_I1 /\ TMCommitAction => Inv15_48a9_R4_0_I1' BY DEF TypeOK,TMCommitAction,TMCommit,Inv15_48a9_R4_0_I1
  \* (Inv15_48a9_R4_0_I1,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv21_4f76_R8_0_I1 /\ Inv15_48a9_R4_0_I1 /\ TMRcvPreparedAction => Inv15_48a9_R4_0_I1' BY DEF TypeOK,Inv21_4f76_R8_0_I1,TMRcvPreparedAction,TMRcvPrepared,Inv15_48a9_R4_0_I1
  \* (Inv15_48a9_R4_0_I1,RMPrepareAction)
  <1>5. TypeOK /\ Inv15_48a9_R4_0_I1 /\ RMPrepareAction => Inv15_48a9_R4_0_I1' BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv15_48a9_R4_0_I1
  \* (Inv15_48a9_R4_0_I1,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv15_48a9_R4_0_I1 /\ RMChooseToAbortAction => Inv15_48a9_R4_0_I1' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv15_48a9_R4_0_I1
  \* (Inv15_48a9_R4_0_I1,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv15_48a9_R4_0_I1 /\ RMRcvCommitMsgAction => Inv15_48a9_R4_0_I1' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv15_48a9_R4_0_I1
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv21_4f76_R8_0_I1
THEOREM L_5 == TypeOK /\ Inv21_4f76_R8_0_I1 /\ Next => Inv21_4f76_R8_0_I1'
  \* (Inv21_4f76_R8_0_I1,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv21_4f76_R8_0_I1 /\ RMRcvAbortMsgAction => Inv21_4f76_R8_0_I1' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv21_4f76_R8_0_I1
  \* (Inv21_4f76_R8_0_I1,TMAbortAction)
  <1>2. TypeOK /\ Inv21_4f76_R8_0_I1 /\ TMAbortAction => Inv21_4f76_R8_0_I1' BY DEF TypeOK,TMAbortAction,TMAbort,Inv21_4f76_R8_0_I1
  \* (Inv21_4f76_R8_0_I1,TMCommitAction)
  <1>3. TypeOK /\ Inv21_4f76_R8_0_I1 /\ TMCommitAction => Inv21_4f76_R8_0_I1' BY DEF TypeOK,TMCommitAction,TMCommit,Inv21_4f76_R8_0_I1
  \* (Inv21_4f76_R8_0_I1,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv21_4f76_R8_0_I1 /\ TMRcvPreparedAction => Inv21_4f76_R8_0_I1' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv21_4f76_R8_0_I1
  \* (Inv21_4f76_R8_0_I1,RMPrepareAction)
  <1>5. TypeOK /\ Inv21_4f76_R8_0_I1 /\ RMPrepareAction => Inv21_4f76_R8_0_I1' BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv21_4f76_R8_0_I1
  \* (Inv21_4f76_R8_0_I1,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv21_4f76_R8_0_I1 /\ RMChooseToAbortAction => Inv21_4f76_R8_0_I1' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv21_4f76_R8_0_I1
  \* (Inv21_4f76_R8_0_I1,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv21_4f76_R8_0_I1 /\ RMRcvCommitMsgAction => Inv21_4f76_R8_0_I1' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv21_4f76_R8_0_I1
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv11_9254_R0_1_I1
THEOREM L_6 == TypeOK /\ Inv53_f69d_R2_1_I1 /\ Inv1_b34d_R2_0_I1 /\ Inv11_9254_R0_1_I1 /\ Next => Inv11_9254_R0_1_I1'
  \* (Inv11_9254_R0_1_I1,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv11_9254_R0_1_I1 /\ RMRcvAbortMsgAction => Inv11_9254_R0_1_I1' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv11_9254_R0_1_I1
  \* (Inv11_9254_R0_1_I1,TMAbortAction)
  <1>2. TypeOK /\ Inv53_f69d_R2_1_I1 /\ Inv11_9254_R0_1_I1 /\ TMAbortAction => Inv11_9254_R0_1_I1' BY DEF TypeOK,Inv53_f69d_R2_1_I1,TMAbortAction,TMAbort,Inv11_9254_R0_1_I1
  \* (Inv11_9254_R0_1_I1,TMCommitAction)
  <1>3. TypeOK /\ Inv11_9254_R0_1_I1 /\ TMCommitAction => Inv11_9254_R0_1_I1' BY DEF TypeOK,TMCommitAction,TMCommit,Inv11_9254_R0_1_I1
  \* (Inv11_9254_R0_1_I1,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv11_9254_R0_1_I1 /\ TMRcvPreparedAction => Inv11_9254_R0_1_I1' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv11_9254_R0_1_I1
  \* (Inv11_9254_R0_1_I1,RMPrepareAction)
  <1>5. TypeOK /\ Inv11_9254_R0_1_I1 /\ RMPrepareAction => Inv11_9254_R0_1_I1' BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv11_9254_R0_1_I1
  \* (Inv11_9254_R0_1_I1,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv11_9254_R0_1_I1 /\ RMChooseToAbortAction => Inv11_9254_R0_1_I1' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv11_9254_R0_1_I1
  \* (Inv11_9254_R0_1_I1,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv1_b34d_R2_0_I1 /\ Inv11_9254_R0_1_I1 /\ RMRcvCommitMsgAction => Inv11_9254_R0_1_I1' BY DEF TypeOK,Inv1_b34d_R2_0_I1,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv11_9254_R0_1_I1
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv1_b34d_R2_0_I1
THEOREM L_7 == TypeOK /\ Inv4_98a2_R5_0_I1 /\ Inv6_2e0f_R5_1_I1 /\ Inv1_b34d_R2_0_I1 /\ Next => Inv1_b34d_R2_0_I1'
  \* (Inv1_b34d_R2_0_I1,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv1_b34d_R2_0_I1 /\ RMRcvAbortMsgAction => Inv1_b34d_R2_0_I1' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv1_b34d_R2_0_I1
  \* (Inv1_b34d_R2_0_I1,TMAbortAction)
  <1>2. TypeOK /\ Inv4_98a2_R5_0_I1 /\ Inv1_b34d_R2_0_I1 /\ TMAbortAction => Inv1_b34d_R2_0_I1' BY DEF TypeOK,Inv4_98a2_R5_0_I1,TMAbortAction,TMAbort,Inv1_b34d_R2_0_I1
  \* (Inv1_b34d_R2_0_I1,TMCommitAction)
  <1>3. TypeOK /\ Inv6_2e0f_R5_1_I1 /\ Inv1_b34d_R2_0_I1 /\ TMCommitAction => Inv1_b34d_R2_0_I1' BY DEF TypeOK,Inv6_2e0f_R5_1_I1,TMCommitAction,TMCommit,Inv1_b34d_R2_0_I1
  \* (Inv1_b34d_R2_0_I1,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv1_b34d_R2_0_I1 /\ TMRcvPreparedAction => Inv1_b34d_R2_0_I1' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv1_b34d_R2_0_I1
  \* (Inv1_b34d_R2_0_I1,RMPrepareAction)
  <1>5. TypeOK /\ Inv1_b34d_R2_0_I1 /\ RMPrepareAction => Inv1_b34d_R2_0_I1' BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv1_b34d_R2_0_I1
  \* (Inv1_b34d_R2_0_I1,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv1_b34d_R2_0_I1 /\ RMChooseToAbortAction => Inv1_b34d_R2_0_I1' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv1_b34d_R2_0_I1
  \* (Inv1_b34d_R2_0_I1,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv1_b34d_R2_0_I1 /\ RMRcvCommitMsgAction => Inv1_b34d_R2_0_I1' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv1_b34d_R2_0_I1
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv4_98a2_R5_0_I1
THEOREM L_8 == TypeOK /\ Inv4_98a2_R5_0_I1 /\ Next => Inv4_98a2_R5_0_I1'
  \* (Inv4_98a2_R5_0_I1,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv4_98a2_R5_0_I1 /\ RMRcvAbortMsgAction => Inv4_98a2_R5_0_I1' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv4_98a2_R5_0_I1
  \* (Inv4_98a2_R5_0_I1,TMAbortAction)
  <1>2. TypeOK /\ Inv4_98a2_R5_0_I1 /\ TMAbortAction => Inv4_98a2_R5_0_I1' BY DEF TypeOK,TMAbortAction,TMAbort,Inv4_98a2_R5_0_I1
  \* (Inv4_98a2_R5_0_I1,TMCommitAction)
  <1>3. TypeOK /\ Inv4_98a2_R5_0_I1 /\ TMCommitAction => Inv4_98a2_R5_0_I1' BY DEF TypeOK,TMCommitAction,TMCommit,Inv4_98a2_R5_0_I1
  \* (Inv4_98a2_R5_0_I1,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv4_98a2_R5_0_I1 /\ TMRcvPreparedAction => Inv4_98a2_R5_0_I1' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv4_98a2_R5_0_I1
  \* (Inv4_98a2_R5_0_I1,RMPrepareAction)
  <1>5. TypeOK /\ Inv4_98a2_R5_0_I1 /\ RMPrepareAction => Inv4_98a2_R5_0_I1' BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv4_98a2_R5_0_I1
  \* (Inv4_98a2_R5_0_I1,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv4_98a2_R5_0_I1 /\ RMChooseToAbortAction => Inv4_98a2_R5_0_I1' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv4_98a2_R5_0_I1
  \* (Inv4_98a2_R5_0_I1,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv4_98a2_R5_0_I1 /\ RMRcvCommitMsgAction => Inv4_98a2_R5_0_I1' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv4_98a2_R5_0_I1
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv6_2e0f_R5_1_I1
THEOREM L_9 == TypeOK /\ Inv6_2e0f_R5_1_I1 /\ Next => Inv6_2e0f_R5_1_I1'
  \* (Inv6_2e0f_R5_1_I1,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv6_2e0f_R5_1_I1 /\ RMRcvAbortMsgAction => Inv6_2e0f_R5_1_I1' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv6_2e0f_R5_1_I1
  \* (Inv6_2e0f_R5_1_I1,TMAbortAction)
  <1>2. TypeOK /\ Inv6_2e0f_R5_1_I1 /\ TMAbortAction => Inv6_2e0f_R5_1_I1' BY DEF TypeOK,TMAbortAction,TMAbort,Inv6_2e0f_R5_1_I1
  \* (Inv6_2e0f_R5_1_I1,TMCommitAction)
  <1>3. TypeOK /\ Inv6_2e0f_R5_1_I1 /\ TMCommitAction => Inv6_2e0f_R5_1_I1' BY DEF TypeOK,TMCommitAction,TMCommit,Inv6_2e0f_R5_1_I1
  \* (Inv6_2e0f_R5_1_I1,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv6_2e0f_R5_1_I1 /\ TMRcvPreparedAction => Inv6_2e0f_R5_1_I1' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv6_2e0f_R5_1_I1
  \* (Inv6_2e0f_R5_1_I1,RMPrepareAction)
  <1>5. TypeOK /\ Inv6_2e0f_R5_1_I1 /\ RMPrepareAction => Inv6_2e0f_R5_1_I1' BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv6_2e0f_R5_1_I1
  \* (Inv6_2e0f_R5_1_I1,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv6_2e0f_R5_1_I1 /\ RMChooseToAbortAction => Inv6_2e0f_R5_1_I1' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv6_2e0f_R5_1_I1
  \* (Inv6_2e0f_R5_1_I1,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv6_2e0f_R5_1_I1 /\ RMRcvCommitMsgAction => Inv6_2e0f_R5_1_I1' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv6_2e0f_R5_1_I1
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv53_f69d_R2_1_I1
THEOREM L_10 == TypeOK /\ Inv4_98a2_R5_0_I1 /\ Inv53_f69d_R2_1_I1 /\ Next => Inv53_f69d_R2_1_I1'
  \* (Inv53_f69d_R2_1_I1,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv53_f69d_R2_1_I1 /\ RMRcvAbortMsgAction => Inv53_f69d_R2_1_I1' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv53_f69d_R2_1_I1
  \* (Inv53_f69d_R2_1_I1,TMAbortAction)
  <1>2. TypeOK /\ Inv53_f69d_R2_1_I1 /\ TMAbortAction => Inv53_f69d_R2_1_I1' BY DEF TypeOK,TMAbortAction,TMAbort,Inv53_f69d_R2_1_I1
  \* (Inv53_f69d_R2_1_I1,TMCommitAction)
  <1>3. TypeOK /\ Inv53_f69d_R2_1_I1 /\ TMCommitAction => Inv53_f69d_R2_1_I1' BY DEF TypeOK,TMCommitAction,TMCommit,Inv53_f69d_R2_1_I1
  \* (Inv53_f69d_R2_1_I1,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv53_f69d_R2_1_I1 /\ TMRcvPreparedAction => Inv53_f69d_R2_1_I1' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv53_f69d_R2_1_I1
  \* (Inv53_f69d_R2_1_I1,RMPrepareAction)
  <1>5. TypeOK /\ Inv53_f69d_R2_1_I1 /\ RMPrepareAction => Inv53_f69d_R2_1_I1' BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv53_f69d_R2_1_I1
  \* (Inv53_f69d_R2_1_I1,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv53_f69d_R2_1_I1 /\ RMChooseToAbortAction => Inv53_f69d_R2_1_I1' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv53_f69d_R2_1_I1
  \* (Inv53_f69d_R2_1_I1,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv4_98a2_R5_0_I1 /\ Inv53_f69d_R2_1_I1 /\ RMRcvCommitMsgAction => Inv53_f69d_R2_1_I1' BY DEF TypeOK,Inv4_98a2_R5_0_I1,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv53_f69d_R2_1_I1
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv23_b2ee_R0_2_I1
THEOREM L_11 == TypeOK /\ Inv1_b34d_R2_0_I1 /\ Inv1448_1fb0_R3_2_I2 /\ Inv2_6383_R1_0_I1 /\ Inv23_b2ee_R0_2_I1 /\ Next => Inv23_b2ee_R0_2_I1'
  \* (Inv23_b2ee_R0_2_I1,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv1_b34d_R2_0_I1 /\ Inv23_b2ee_R0_2_I1 /\ RMRcvAbortMsgAction => Inv23_b2ee_R0_2_I1' BY DEF TypeOK,Inv1_b34d_R2_0_I1,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv23_b2ee_R0_2_I1
  \* (Inv23_b2ee_R0_2_I1,TMAbortAction)
  <1>2. TypeOK /\ Inv23_b2ee_R0_2_I1 /\ TMAbortAction => Inv23_b2ee_R0_2_I1' BY DEF TypeOK,TMAbortAction,TMAbort,Inv23_b2ee_R0_2_I1
  \* (Inv23_b2ee_R0_2_I1,TMCommitAction)
  <1>3. TypeOK /\ Inv1448_1fb0_R3_2_I2 /\ Inv23_b2ee_R0_2_I1 /\ TMCommitAction => Inv23_b2ee_R0_2_I1' BY DEF TypeOK,Inv1448_1fb0_R3_2_I2,TMCommitAction,TMCommit,Inv23_b2ee_R0_2_I1
  \* (Inv23_b2ee_R0_2_I1,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv23_b2ee_R0_2_I1 /\ TMRcvPreparedAction => Inv23_b2ee_R0_2_I1' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv23_b2ee_R0_2_I1
  \* (Inv23_b2ee_R0_2_I1,RMPrepareAction)
  <1>5. TypeOK /\ Inv23_b2ee_R0_2_I1 /\ RMPrepareAction => Inv23_b2ee_R0_2_I1' BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv23_b2ee_R0_2_I1
  \* (Inv23_b2ee_R0_2_I1,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv2_6383_R1_0_I1 /\ Inv23_b2ee_R0_2_I1 /\ RMChooseToAbortAction => Inv23_b2ee_R0_2_I1' BY DEF TypeOK,Inv2_6383_R1_0_I1,RMChooseToAbortAction,RMChooseToAbort,Inv23_b2ee_R0_2_I1
  \* (Inv23_b2ee_R0_2_I1,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv23_b2ee_R0_2_I1 /\ RMRcvCommitMsgAction => Inv23_b2ee_R0_2_I1' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv23_b2ee_R0_2_I1
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv1448_1fb0_R3_2_I2
THEOREM L_12 == TypeOK /\ Inv6_2e0f_R5_1_I1 /\ Inv1449_35cb_R7_2_I2 /\ Inv4_98a2_R5_0_I1 /\ Inv1448_1fb0_R3_2_I2 /\ Next => Inv1448_1fb0_R3_2_I2'
  \* (Inv1448_1fb0_R3_2_I2,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv6_2e0f_R5_1_I1 /\ Inv1448_1fb0_R3_2_I2 /\ RMRcvAbortMsgAction => Inv1448_1fb0_R3_2_I2' BY DEF TypeOK,Inv6_2e0f_R5_1_I1,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv1448_1fb0_R3_2_I2
  \* (Inv1448_1fb0_R3_2_I2,TMAbortAction)
  <1>2. TypeOK /\ Inv1448_1fb0_R3_2_I2 /\ TMAbortAction => Inv1448_1fb0_R3_2_I2' BY DEF TypeOK,TMAbortAction,TMAbort,Inv1448_1fb0_R3_2_I2
  \* (Inv1448_1fb0_R3_2_I2,TMCommitAction)
  <1>3. TypeOK /\ Inv1448_1fb0_R3_2_I2 /\ TMCommitAction => Inv1448_1fb0_R3_2_I2' BY DEF TypeOK,TMCommitAction,TMCommit,Inv1448_1fb0_R3_2_I2
  \* (Inv1448_1fb0_R3_2_I2,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv1449_35cb_R7_2_I2 /\ Inv1448_1fb0_R3_2_I2 /\ TMRcvPreparedAction => Inv1448_1fb0_R3_2_I2' BY DEF TypeOK,Inv1449_35cb_R7_2_I2,TMRcvPreparedAction,TMRcvPrepared,Inv1448_1fb0_R3_2_I2
  \* (Inv1448_1fb0_R3_2_I2,RMPrepareAction)
  <1>5. TypeOK /\ Inv1448_1fb0_R3_2_I2 /\ RMPrepareAction => Inv1448_1fb0_R3_2_I2' BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv1448_1fb0_R3_2_I2
  \* (Inv1448_1fb0_R3_2_I2,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv1448_1fb0_R3_2_I2 /\ RMChooseToAbortAction => Inv1448_1fb0_R3_2_I2' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv1448_1fb0_R3_2_I2
  \* (Inv1448_1fb0_R3_2_I2,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv4_98a2_R5_0_I1 /\ Inv1448_1fb0_R3_2_I2 /\ RMRcvCommitMsgAction => Inv1448_1fb0_R3_2_I2' BY DEF TypeOK,Inv4_98a2_R5_0_I1,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv1448_1fb0_R3_2_I2
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv1449_35cb_R7_2_I2
THEOREM L_13 == TypeOK /\ Inv6_2e0f_R5_1_I1 /\ Inv4_98a2_R5_0_I1 /\ Inv1449_35cb_R7_2_I2 /\ Next => Inv1449_35cb_R7_2_I2'
  \* (Inv1449_35cb_R7_2_I2,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv6_2e0f_R5_1_I1 /\ Inv1449_35cb_R7_2_I2 /\ RMRcvAbortMsgAction => Inv1449_35cb_R7_2_I2' BY DEF TypeOK,Inv6_2e0f_R5_1_I1,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv1449_35cb_R7_2_I2
  \* (Inv1449_35cb_R7_2_I2,TMAbortAction)
  <1>2. TypeOK /\ Inv1449_35cb_R7_2_I2 /\ TMAbortAction => Inv1449_35cb_R7_2_I2' BY DEF TypeOK,TMAbortAction,TMAbort,Inv1449_35cb_R7_2_I2
  \* (Inv1449_35cb_R7_2_I2,TMCommitAction)
  <1>3. TypeOK /\ Inv1449_35cb_R7_2_I2 /\ TMCommitAction => Inv1449_35cb_R7_2_I2' BY DEF TypeOK,TMCommitAction,TMCommit,Inv1449_35cb_R7_2_I2
  \* (Inv1449_35cb_R7_2_I2,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv1449_35cb_R7_2_I2 /\ TMRcvPreparedAction => Inv1449_35cb_R7_2_I2' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv1449_35cb_R7_2_I2
  \* (Inv1449_35cb_R7_2_I2,RMPrepareAction)
  <1>5. TypeOK /\ Inv1449_35cb_R7_2_I2 /\ RMPrepareAction => Inv1449_35cb_R7_2_I2' BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv1449_35cb_R7_2_I2
  \* (Inv1449_35cb_R7_2_I2,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv1449_35cb_R7_2_I2 /\ RMChooseToAbortAction => Inv1449_35cb_R7_2_I2' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv1449_35cb_R7_2_I2
  \* (Inv1449_35cb_R7_2_I2,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv4_98a2_R5_0_I1 /\ Inv1449_35cb_R7_2_I2 /\ RMRcvCommitMsgAction => Inv1449_35cb_R7_2_I2' BY DEF TypeOK,Inv4_98a2_R5_0_I1,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv1449_35cb_R7_2_I2
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal, H_TCConsistent
    <1>2. Init => Inv73_bad3_R0_0_I1 BY DEF Init, Inv73_bad3_R0_0_I1, IndGlobal
    <1>3. Init => Inv2_6383_R1_0_I1 BY DEF Init, Inv2_6383_R1_0_I1, IndGlobal
    <1>4. Init => Inv15_48a9_R4_0_I1 BY DEF Init, Inv15_48a9_R4_0_I1, IndGlobal
    <1>5. Init => Inv21_4f76_R8_0_I1 BY DEF Init, Inv21_4f76_R8_0_I1, IndGlobal
    <1>6. Init => Inv11_9254_R0_1_I1 BY DEF Init, Inv11_9254_R0_1_I1, IndGlobal
    <1>7. Init => Inv1_b34d_R2_0_I1 BY DEF Init, Inv1_b34d_R2_0_I1, IndGlobal
    <1>8. Init => Inv4_98a2_R5_0_I1 BY DEF Init, Inv4_98a2_R5_0_I1, IndGlobal
    <1>9. Init => Inv6_2e0f_R5_1_I1 BY DEF Init, Inv6_2e0f_R5_1_I1, IndGlobal
    <1>10. Init => Inv53_f69d_R2_1_I1 BY DEF Init, Inv53_f69d_R2_1_I1, IndGlobal
    <1>11. Init => Inv23_b2ee_R0_2_I1 BY DEF Init, Inv23_b2ee_R0_2_I1, IndGlobal
    <1>12. Init => Inv1448_1fb0_R3_2_I2 BY DEF Init, Inv1448_1fb0_R3_2_I2, IndGlobal
    <1>13. Init => Inv1449_35cb_R7_2_I2 BY DEF Init, Inv1449_35cb_R7_2_I2, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13 DEF Next, IndGlobal

====
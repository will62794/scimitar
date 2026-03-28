---- MODULE TwoPhase_IndProofs_nfm ----
EXTENDS TwoPhase,TLAPS

\* Proof Graph Stats
\* ==================
\* seed: None
\* num proof graph nodes: 16
\* num proof obligations: 112

IndGlobal == 
  /\ TypeOK
  /\ H_TCConsistent
  /\ H_RMCommittedImpliesNoRMsWorking
  /\ H_RMCommittedImpliesNoAbortMsg
  /\ H_RMAbortedImpliesNoCommitMsg
  /\ H_CommitSentImpliesRMsNotWorking
  /\ H_RMCommittedImpliesTMCommitted
  /\ H_CommitMsgImpliesNoAbortMsg
  /\ H_RMWorkingImpliesNoCommitMsg
  /\ H_RMAbortedAndPreparedImpliesTMAborted
  /\ H_TMKnowsPrepareImpliesRMWorking
  /\ H_CommitMsgImpliesTMCommitted
  /\ H_InitNoCommitMsg
  /\ H_InitNoAbortMsg
  /\ H_RMWorkingImpliesNotPrepared
  /\ H_RMSentPrepareImpliesNotWorking
  /\ H_AbortMsgImpliesTMAborted


\* mean in-degree: 1.375
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


\*** H_AbortMsgImpliesTMAborted
THEOREM L_1 == TypeOK /\ H_AbortMsgImpliesTMAborted /\ Next => H_AbortMsgImpliesTMAborted'
  \* (H_AbortMsgImpliesTMAborted,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ H_AbortMsgImpliesTMAborted /\ RMRcvAbortMsgAction => H_AbortMsgImpliesTMAborted' 
    <2> SUFFICES ASSUME TypeOK,
                        H_AbortMsgImpliesTMAborted,
                        TRUE,
                        NEW rm \in RM,
                        RMRcvAbortMsg(rm),
                        ([type |-> "Abort"] \in msgsAbortCommit)'
                 PROVE  (tmState = "aborted")'
      BY DEF H_AbortMsgImpliesTMAborted, RMRcvAbortMsgAction
    <2> QED
      BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,H_AbortMsgImpliesTMAborted
  \* (H_AbortMsgImpliesTMAborted,TMAbortAction)
  <1>2. TypeOK /\ H_AbortMsgImpliesTMAborted /\ TMAbortAction => H_AbortMsgImpliesTMAborted' BY DEF TypeOK,TMAbortAction,TMAbort,H_AbortMsgImpliesTMAborted
  \* (H_AbortMsgImpliesTMAborted,TMCommitAction)
  <1>3. TypeOK /\ H_AbortMsgImpliesTMAborted /\ TMCommitAction => H_AbortMsgImpliesTMAborted' BY DEF TypeOK,TMCommitAction,TMCommit,H_AbortMsgImpliesTMAborted
  \* (H_AbortMsgImpliesTMAborted,TMRcvPreparedAction)
  <1>4. TypeOK /\ H_AbortMsgImpliesTMAborted /\ TMRcvPreparedAction => H_AbortMsgImpliesTMAborted' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,H_AbortMsgImpliesTMAborted
  \* (H_AbortMsgImpliesTMAborted,RMPrepareAction)
  <1>5. TypeOK /\ H_AbortMsgImpliesTMAborted /\ RMPrepareAction => H_AbortMsgImpliesTMAborted' BY DEF TypeOK,RMPrepareAction,RMPrepare,H_AbortMsgImpliesTMAborted
  \* (H_AbortMsgImpliesTMAborted,RMChooseToAbortAction)
  <1>6. TypeOK /\ H_AbortMsgImpliesTMAborted /\ RMChooseToAbortAction => H_AbortMsgImpliesTMAborted' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,H_AbortMsgImpliesTMAborted
  \* (H_AbortMsgImpliesTMAborted,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ H_AbortMsgImpliesTMAborted /\ RMRcvCommitMsgAction => H_AbortMsgImpliesTMAborted' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,H_AbortMsgImpliesTMAborted
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** H_RMSentPrepareImpliesNotWorking
THEOREM L_2 == TypeOK /\ H_RMSentPrepareImpliesNotWorking /\ Next => H_RMSentPrepareImpliesNotWorking'
  \* (H_RMSentPrepareImpliesNotWorking,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ H_RMSentPrepareImpliesNotWorking /\ RMRcvAbortMsgAction => H_RMSentPrepareImpliesNotWorking' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,H_RMSentPrepareImpliesNotWorking
  \* (H_RMSentPrepareImpliesNotWorking,TMAbortAction)
  <1>2. TypeOK /\ H_RMSentPrepareImpliesNotWorking /\ TMAbortAction => H_RMSentPrepareImpliesNotWorking' BY DEF TypeOK,TMAbortAction,TMAbort,H_RMSentPrepareImpliesNotWorking
  \* (H_RMSentPrepareImpliesNotWorking,TMCommitAction)
  <1>3. TypeOK /\ H_RMSentPrepareImpliesNotWorking /\ TMCommitAction => H_RMSentPrepareImpliesNotWorking' BY DEF TypeOK,TMCommitAction,TMCommit,H_RMSentPrepareImpliesNotWorking
  \* (H_RMSentPrepareImpliesNotWorking,TMRcvPreparedAction)
  <1>4. TypeOK /\ H_RMSentPrepareImpliesNotWorking /\ TMRcvPreparedAction => H_RMSentPrepareImpliesNotWorking' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,H_RMSentPrepareImpliesNotWorking
  \* (H_RMSentPrepareImpliesNotWorking,RMPrepareAction)
  <1>5. TypeOK /\ H_RMSentPrepareImpliesNotWorking /\ RMPrepareAction => H_RMSentPrepareImpliesNotWorking' BY DEF TypeOK,RMPrepareAction,RMPrepare,H_RMSentPrepareImpliesNotWorking
  \* (H_RMSentPrepareImpliesNotWorking,RMChooseToAbortAction)
  <1>6. TypeOK /\ H_RMSentPrepareImpliesNotWorking /\ RMChooseToAbortAction => H_RMSentPrepareImpliesNotWorking' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,H_RMSentPrepareImpliesNotWorking
  \* (H_RMSentPrepareImpliesNotWorking,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ H_RMSentPrepareImpliesNotWorking /\ RMRcvCommitMsgAction => H_RMSentPrepareImpliesNotWorking' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,H_RMSentPrepareImpliesNotWorking
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** H_RMWorkingImpliesNotPrepared
THEOREM L_3 == TypeOK /\ H_RMSentPrepareImpliesNotWorking /\ H_RMWorkingImpliesNotPrepared /\ Next => H_RMWorkingImpliesNotPrepared'
  \* (H_RMWorkingImpliesNotPrepared,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ H_RMWorkingImpliesNotPrepared /\ RMRcvAbortMsgAction => H_RMWorkingImpliesNotPrepared' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,H_RMWorkingImpliesNotPrepared
  \* (H_RMWorkingImpliesNotPrepared,TMAbortAction)
  <1>2. TypeOK /\ H_RMWorkingImpliesNotPrepared /\ TMAbortAction => H_RMWorkingImpliesNotPrepared' BY DEF TypeOK,TMAbortAction,TMAbort,H_RMWorkingImpliesNotPrepared
  \* (H_RMWorkingImpliesNotPrepared,TMCommitAction)
  <1>3. TypeOK /\ H_RMWorkingImpliesNotPrepared /\ TMCommitAction => H_RMWorkingImpliesNotPrepared' BY DEF TypeOK,TMCommitAction,TMCommit,H_RMWorkingImpliesNotPrepared
  \* (H_RMWorkingImpliesNotPrepared,TMRcvPreparedAction)
  <1>4. TypeOK /\ H_RMSentPrepareImpliesNotWorking /\ H_RMWorkingImpliesNotPrepared /\ TMRcvPreparedAction => H_RMWorkingImpliesNotPrepared' BY DEF TypeOK,H_RMSentPrepareImpliesNotWorking,TMRcvPreparedAction,TMRcvPrepared,H_RMWorkingImpliesNotPrepared
  \* (H_RMWorkingImpliesNotPrepared,RMPrepareAction)
  <1>5. TypeOK /\ H_RMWorkingImpliesNotPrepared /\ RMPrepareAction => H_RMWorkingImpliesNotPrepared' BY DEF TypeOK,RMPrepareAction,RMPrepare,H_RMWorkingImpliesNotPrepared
  \* (H_RMWorkingImpliesNotPrepared,RMChooseToAbortAction)
  <1>6. TypeOK /\ H_RMWorkingImpliesNotPrepared /\ RMChooseToAbortAction => H_RMWorkingImpliesNotPrepared' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,H_RMWorkingImpliesNotPrepared
  \* (H_RMWorkingImpliesNotPrepared,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ H_RMWorkingImpliesNotPrepared /\ RMRcvCommitMsgAction => H_RMWorkingImpliesNotPrepared' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,H_RMWorkingImpliesNotPrepared
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** H_InitNoAbortMsg
THEOREM L_4 == TypeOK /\ H_InitNoAbortMsg /\ Next => H_InitNoAbortMsg'
  \* (H_InitNoAbortMsg,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ H_InitNoAbortMsg /\ RMRcvAbortMsgAction => H_InitNoAbortMsg' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,H_InitNoAbortMsg
  \* (H_InitNoAbortMsg,TMAbortAction)
  <1>2. TypeOK /\ H_InitNoAbortMsg /\ TMAbortAction => H_InitNoAbortMsg' BY DEF TypeOK,TMAbortAction,TMAbort,H_InitNoAbortMsg
  \* (H_InitNoAbortMsg,TMCommitAction)
  <1>3. TypeOK /\ H_InitNoAbortMsg /\ TMCommitAction => H_InitNoAbortMsg' BY DEF TypeOK,TMCommitAction,TMCommit,H_InitNoAbortMsg
  \* (H_InitNoAbortMsg,TMRcvPreparedAction)
  <1>4. TypeOK /\ H_InitNoAbortMsg /\ TMRcvPreparedAction => H_InitNoAbortMsg' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,H_InitNoAbortMsg
  \* (H_InitNoAbortMsg,RMPrepareAction)
  <1>5. TypeOK /\ H_InitNoAbortMsg /\ RMPrepareAction => H_InitNoAbortMsg' BY DEF TypeOK,RMPrepareAction,RMPrepare,H_InitNoAbortMsg
  \* (H_InitNoAbortMsg,RMChooseToAbortAction)
  <1>6. TypeOK /\ H_InitNoAbortMsg /\ RMChooseToAbortAction => H_InitNoAbortMsg' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,H_InitNoAbortMsg
  \* (H_InitNoAbortMsg,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ H_InitNoAbortMsg /\ RMRcvCommitMsgAction => H_InitNoAbortMsg' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,H_InitNoAbortMsg
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** H_InitNoCommitMsg
THEOREM L_5 == TypeOK /\ H_InitNoCommitMsg /\ Next => H_InitNoCommitMsg'
  \* (H_InitNoCommitMsg,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ H_InitNoCommitMsg /\ RMRcvAbortMsgAction => H_InitNoCommitMsg' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,H_InitNoCommitMsg
  \* (H_InitNoCommitMsg,TMAbortAction)
  <1>2. TypeOK /\ H_InitNoCommitMsg /\ TMAbortAction => H_InitNoCommitMsg' BY DEF TypeOK,TMAbortAction,TMAbort,H_InitNoCommitMsg
  \* (H_InitNoCommitMsg,TMCommitAction)
  <1>3. TypeOK /\ H_InitNoCommitMsg /\ TMCommitAction => H_InitNoCommitMsg' BY DEF TypeOK,TMCommitAction,TMCommit,H_InitNoCommitMsg
  \* (H_InitNoCommitMsg,TMRcvPreparedAction)
  <1>4. TypeOK /\ H_InitNoCommitMsg /\ TMRcvPreparedAction => H_InitNoCommitMsg' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,H_InitNoCommitMsg
  \* (H_InitNoCommitMsg,RMPrepareAction)
  <1>5. TypeOK /\ H_InitNoCommitMsg /\ RMPrepareAction => H_InitNoCommitMsg' BY DEF TypeOK,RMPrepareAction,RMPrepare,H_InitNoCommitMsg
  \* (H_InitNoCommitMsg,RMChooseToAbortAction)
  <1>6. TypeOK /\ H_InitNoCommitMsg /\ RMChooseToAbortAction => H_InitNoCommitMsg' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,H_InitNoCommitMsg
  \* (H_InitNoCommitMsg,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ H_InitNoCommitMsg /\ RMRcvCommitMsgAction => H_InitNoCommitMsg' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,H_InitNoCommitMsg
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** H_CommitMsgImpliesTMCommitted
THEOREM L_6 == TypeOK /\ H_CommitMsgImpliesTMCommitted /\ Next => H_CommitMsgImpliesTMCommitted'
  \* (H_CommitMsgImpliesTMCommitted,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ H_CommitMsgImpliesTMCommitted /\ RMRcvAbortMsgAction => H_CommitMsgImpliesTMCommitted' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,H_CommitMsgImpliesTMCommitted
  \* (H_CommitMsgImpliesTMCommitted,TMAbortAction)
  <1>2. TypeOK /\ H_CommitMsgImpliesTMCommitted /\ TMAbortAction => H_CommitMsgImpliesTMCommitted' BY DEF TypeOK,TMAbortAction,TMAbort,H_CommitMsgImpliesTMCommitted
  \* (H_CommitMsgImpliesTMCommitted,TMCommitAction)
  <1>3. TypeOK /\ H_CommitMsgImpliesTMCommitted /\ TMCommitAction => H_CommitMsgImpliesTMCommitted' BY DEF TypeOK,TMCommitAction,TMCommit,H_CommitMsgImpliesTMCommitted
  \* (H_CommitMsgImpliesTMCommitted,TMRcvPreparedAction)
  <1>4. TypeOK /\ H_CommitMsgImpliesTMCommitted /\ TMRcvPreparedAction => H_CommitMsgImpliesTMCommitted' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,H_CommitMsgImpliesTMCommitted
  \* (H_CommitMsgImpliesTMCommitted,RMPrepareAction)
  <1>5. TypeOK /\ H_CommitMsgImpliesTMCommitted /\ RMPrepareAction => H_CommitMsgImpliesTMCommitted' BY DEF TypeOK,RMPrepareAction,RMPrepare,H_CommitMsgImpliesTMCommitted
  \* (H_CommitMsgImpliesTMCommitted,RMChooseToAbortAction)
  <1>6. TypeOK /\ H_CommitMsgImpliesTMCommitted /\ RMChooseToAbortAction => H_CommitMsgImpliesTMCommitted' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,H_CommitMsgImpliesTMCommitted
  \* (H_CommitMsgImpliesTMCommitted,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ H_CommitMsgImpliesTMCommitted /\ RMRcvCommitMsgAction => H_CommitMsgImpliesTMCommitted' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,H_CommitMsgImpliesTMCommitted
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** H_TMKnowsPrepareImpliesRMWorking
THEOREM L_7 == TypeOK /\ H_RMSentPrepareImpliesNotWorking /\ H_TMKnowsPrepareImpliesRMWorking /\ Next => H_TMKnowsPrepareImpliesRMWorking'
  \* (H_TMKnowsPrepareImpliesRMWorking,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ H_TMKnowsPrepareImpliesRMWorking /\ RMRcvAbortMsgAction => H_TMKnowsPrepareImpliesRMWorking' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,H_TMKnowsPrepareImpliesRMWorking
  \* (H_TMKnowsPrepareImpliesRMWorking,TMAbortAction)
  <1>2. TypeOK /\ H_TMKnowsPrepareImpliesRMWorking /\ TMAbortAction => H_TMKnowsPrepareImpliesRMWorking' BY DEF TypeOK,TMAbortAction,TMAbort,H_TMKnowsPrepareImpliesRMWorking
  \* (H_TMKnowsPrepareImpliesRMWorking,TMCommitAction)
  <1>3. TypeOK /\ H_TMKnowsPrepareImpliesRMWorking /\ TMCommitAction => H_TMKnowsPrepareImpliesRMWorking' BY DEF TypeOK,TMCommitAction,TMCommit,H_TMKnowsPrepareImpliesRMWorking
  \* (H_TMKnowsPrepareImpliesRMWorking,TMRcvPreparedAction)
  <1>4. TypeOK /\ H_RMSentPrepareImpliesNotWorking /\ H_TMKnowsPrepareImpliesRMWorking /\ TMRcvPreparedAction => H_TMKnowsPrepareImpliesRMWorking' BY DEF TypeOK,H_RMSentPrepareImpliesNotWorking,TMRcvPreparedAction,TMRcvPrepared,H_TMKnowsPrepareImpliesRMWorking
  \* (H_TMKnowsPrepareImpliesRMWorking,RMPrepareAction)
  <1>5. TypeOK /\ H_TMKnowsPrepareImpliesRMWorking /\ RMPrepareAction => H_TMKnowsPrepareImpliesRMWorking' BY DEF TypeOK,RMPrepareAction,RMPrepare,H_TMKnowsPrepareImpliesRMWorking
  \* (H_TMKnowsPrepareImpliesRMWorking,RMChooseToAbortAction)
  <1>6. TypeOK /\ H_TMKnowsPrepareImpliesRMWorking /\ RMChooseToAbortAction => H_TMKnowsPrepareImpliesRMWorking' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,H_TMKnowsPrepareImpliesRMWorking
  \* (H_TMKnowsPrepareImpliesRMWorking,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ H_TMKnowsPrepareImpliesRMWorking /\ RMRcvCommitMsgAction => H_TMKnowsPrepareImpliesRMWorking' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,H_TMKnowsPrepareImpliesRMWorking
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** H_RMAbortedAndPreparedImpliesTMAborted
THEOREM L_8 == TypeOK /\ H_AbortMsgImpliesTMAborted /\ H_TMKnowsPrepareImpliesRMWorking /\ H_RMSentPrepareImpliesNotWorking /\ H_RMAbortedAndPreparedImpliesTMAborted /\ Next => H_RMAbortedAndPreparedImpliesTMAborted'
  \* (H_RMAbortedAndPreparedImpliesTMAborted,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ H_AbortMsgImpliesTMAborted /\ H_RMAbortedAndPreparedImpliesTMAborted /\ RMRcvAbortMsgAction => H_RMAbortedAndPreparedImpliesTMAborted' BY DEF TypeOK,H_AbortMsgImpliesTMAborted,RMRcvAbortMsgAction,RMRcvAbortMsg,H_RMAbortedAndPreparedImpliesTMAborted
  \* (H_RMAbortedAndPreparedImpliesTMAborted,TMAbortAction)
  <1>2. TypeOK /\ H_RMAbortedAndPreparedImpliesTMAborted /\ TMAbortAction => H_RMAbortedAndPreparedImpliesTMAborted' BY DEF TypeOK,TMAbortAction,TMAbort,H_RMAbortedAndPreparedImpliesTMAborted
  \* (H_RMAbortedAndPreparedImpliesTMAborted,TMCommitAction)
  <1>3. TypeOK /\ H_RMAbortedAndPreparedImpliesTMAborted /\ TMCommitAction => H_RMAbortedAndPreparedImpliesTMAborted' BY DEF TypeOK,TMCommitAction,TMCommit,H_RMAbortedAndPreparedImpliesTMAborted
  \* (H_RMAbortedAndPreparedImpliesTMAborted,TMRcvPreparedAction)
  <1>4. TypeOK /\ H_RMAbortedAndPreparedImpliesTMAborted /\ TMRcvPreparedAction => H_RMAbortedAndPreparedImpliesTMAborted' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,H_RMAbortedAndPreparedImpliesTMAborted
  \* (H_RMAbortedAndPreparedImpliesTMAborted,RMPrepareAction)
  <1>5. TypeOK /\ H_RMAbortedAndPreparedImpliesTMAborted /\ RMPrepareAction => H_RMAbortedAndPreparedImpliesTMAborted' BY DEF TypeOK,RMPrepareAction,RMPrepare,H_RMAbortedAndPreparedImpliesTMAborted
  \* (H_RMAbortedAndPreparedImpliesTMAborted,RMChooseToAbortAction)
  <1>6. TypeOK /\ H_TMKnowsPrepareImpliesRMWorking /\ H_RMSentPrepareImpliesNotWorking /\ H_RMAbortedAndPreparedImpliesTMAborted /\ RMChooseToAbortAction => H_RMAbortedAndPreparedImpliesTMAborted' BY DEF TypeOK,H_TMKnowsPrepareImpliesRMWorking,H_RMSentPrepareImpliesNotWorking,RMChooseToAbortAction,RMChooseToAbort,H_RMAbortedAndPreparedImpliesTMAborted
  \* (H_RMAbortedAndPreparedImpliesTMAborted,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ H_RMAbortedAndPreparedImpliesTMAborted /\ RMRcvCommitMsgAction => H_RMAbortedAndPreparedImpliesTMAborted' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,H_RMAbortedAndPreparedImpliesTMAborted
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** H_RMWorkingImpliesNoCommitMsg
THEOREM L_9 == TypeOK /\ H_RMWorkingImpliesNotPrepared /\ H_RMWorkingImpliesNoCommitMsg /\ Next => H_RMWorkingImpliesNoCommitMsg'
  \* (H_RMWorkingImpliesNoCommitMsg,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ H_RMWorkingImpliesNoCommitMsg /\ RMRcvAbortMsgAction => H_RMWorkingImpliesNoCommitMsg' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,H_RMWorkingImpliesNoCommitMsg
  \* (H_RMWorkingImpliesNoCommitMsg,TMAbortAction)
  <1>2. TypeOK /\ H_RMWorkingImpliesNoCommitMsg /\ TMAbortAction => H_RMWorkingImpliesNoCommitMsg' BY DEF TypeOK,TMAbortAction,TMAbort,H_RMWorkingImpliesNoCommitMsg
  \* (H_RMWorkingImpliesNoCommitMsg,TMCommitAction)
  <1>3. TypeOK /\ H_RMWorkingImpliesNotPrepared /\ H_RMWorkingImpliesNoCommitMsg /\ TMCommitAction => H_RMWorkingImpliesNoCommitMsg' BY DEF TypeOK,H_RMWorkingImpliesNotPrepared,TMCommitAction,TMCommit,H_RMWorkingImpliesNoCommitMsg
  \* (H_RMWorkingImpliesNoCommitMsg,TMRcvPreparedAction)
  <1>4. TypeOK /\ H_RMWorkingImpliesNoCommitMsg /\ TMRcvPreparedAction => H_RMWorkingImpliesNoCommitMsg' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,H_RMWorkingImpliesNoCommitMsg
  \* (H_RMWorkingImpliesNoCommitMsg,RMPrepareAction)
  <1>5. TypeOK /\ H_RMWorkingImpliesNoCommitMsg /\ RMPrepareAction => H_RMWorkingImpliesNoCommitMsg' BY DEF TypeOK,RMPrepareAction,RMPrepare,H_RMWorkingImpliesNoCommitMsg
  \* (H_RMWorkingImpliesNoCommitMsg,RMChooseToAbortAction)
  <1>6. TypeOK /\ H_RMWorkingImpliesNoCommitMsg /\ RMChooseToAbortAction => H_RMWorkingImpliesNoCommitMsg' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,H_RMWorkingImpliesNoCommitMsg
  \* (H_RMWorkingImpliesNoCommitMsg,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ H_RMWorkingImpliesNoCommitMsg /\ RMRcvCommitMsgAction => H_RMWorkingImpliesNoCommitMsg' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,H_RMWorkingImpliesNoCommitMsg
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** H_CommitMsgImpliesNoAbortMsg
THEOREM L_10 == TypeOK /\ H_InitNoCommitMsg /\ H_InitNoAbortMsg /\ H_CommitMsgImpliesNoAbortMsg /\ Next => H_CommitMsgImpliesNoAbortMsg'
  \* (H_CommitMsgImpliesNoAbortMsg,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ H_CommitMsgImpliesNoAbortMsg /\ RMRcvAbortMsgAction => H_CommitMsgImpliesNoAbortMsg' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,H_CommitMsgImpliesNoAbortMsg
  \* (H_CommitMsgImpliesNoAbortMsg,TMAbortAction)
  <1>2. TypeOK /\ H_InitNoCommitMsg /\ H_CommitMsgImpliesNoAbortMsg /\ TMAbortAction => H_CommitMsgImpliesNoAbortMsg' BY DEF TypeOK,H_InitNoCommitMsg,TMAbortAction,TMAbort,H_CommitMsgImpliesNoAbortMsg
  \* (H_CommitMsgImpliesNoAbortMsg,TMCommitAction)
  <1>3. TypeOK /\ H_InitNoAbortMsg /\ H_CommitMsgImpliesNoAbortMsg /\ TMCommitAction => H_CommitMsgImpliesNoAbortMsg' BY DEF TypeOK,H_InitNoAbortMsg,TMCommitAction,TMCommit,H_CommitMsgImpliesNoAbortMsg
  \* (H_CommitMsgImpliesNoAbortMsg,TMRcvPreparedAction)
  <1>4. TypeOK /\ H_CommitMsgImpliesNoAbortMsg /\ TMRcvPreparedAction => H_CommitMsgImpliesNoAbortMsg' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,H_CommitMsgImpliesNoAbortMsg
  \* (H_CommitMsgImpliesNoAbortMsg,RMPrepareAction)
  <1>5. TypeOK /\ H_CommitMsgImpliesNoAbortMsg /\ RMPrepareAction => H_CommitMsgImpliesNoAbortMsg' BY DEF TypeOK,RMPrepareAction,RMPrepare,H_CommitMsgImpliesNoAbortMsg
  \* (H_CommitMsgImpliesNoAbortMsg,RMChooseToAbortAction)
  <1>6. TypeOK /\ H_CommitMsgImpliesNoAbortMsg /\ RMChooseToAbortAction => H_CommitMsgImpliesNoAbortMsg' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,H_CommitMsgImpliesNoAbortMsg
  \* (H_CommitMsgImpliesNoAbortMsg,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ H_CommitMsgImpliesNoAbortMsg /\ RMRcvCommitMsgAction => H_CommitMsgImpliesNoAbortMsg' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,H_CommitMsgImpliesNoAbortMsg
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** H_RMCommittedImpliesTMCommitted
THEOREM L_11 == TypeOK /\ H_CommitMsgImpliesTMCommitted /\ H_RMCommittedImpliesTMCommitted /\ Next => H_RMCommittedImpliesTMCommitted'
  \* (H_RMCommittedImpliesTMCommitted,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ H_RMCommittedImpliesTMCommitted /\ RMRcvAbortMsgAction => H_RMCommittedImpliesTMCommitted' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,H_RMCommittedImpliesTMCommitted
  \* (H_RMCommittedImpliesTMCommitted,TMAbortAction)
  <1>2. TypeOK /\ H_RMCommittedImpliesTMCommitted /\ TMAbortAction => H_RMCommittedImpliesTMCommitted' BY DEF TypeOK,TMAbortAction,TMAbort,H_RMCommittedImpliesTMCommitted
  \* (H_RMCommittedImpliesTMCommitted,TMCommitAction)
  <1>3. TypeOK /\ H_RMCommittedImpliesTMCommitted /\ TMCommitAction => H_RMCommittedImpliesTMCommitted' BY DEF TypeOK,TMCommitAction,TMCommit,H_RMCommittedImpliesTMCommitted
  \* (H_RMCommittedImpliesTMCommitted,TMRcvPreparedAction)
  <1>4. TypeOK /\ H_RMCommittedImpliesTMCommitted /\ TMRcvPreparedAction => H_RMCommittedImpliesTMCommitted' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,H_RMCommittedImpliesTMCommitted
  \* (H_RMCommittedImpliesTMCommitted,RMPrepareAction)
  <1>5. TypeOK /\ H_RMCommittedImpliesTMCommitted /\ RMPrepareAction => H_RMCommittedImpliesTMCommitted' BY DEF TypeOK,RMPrepareAction,RMPrepare,H_RMCommittedImpliesTMCommitted
  \* (H_RMCommittedImpliesTMCommitted,RMChooseToAbortAction)
  <1>6. TypeOK /\ H_RMCommittedImpliesTMCommitted /\ RMChooseToAbortAction => H_RMCommittedImpliesTMCommitted' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,H_RMCommittedImpliesTMCommitted
  \* (H_RMCommittedImpliesTMCommitted,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ H_CommitMsgImpliesTMCommitted /\ H_RMCommittedImpliesTMCommitted /\ RMRcvCommitMsgAction => H_RMCommittedImpliesTMCommitted' 
    <2> SUFFICES ASSUME TypeOK /\ H_CommitMsgImpliesTMCommitted /\ H_RMCommittedImpliesTMCommitted /\ RMRcvCommitMsgAction,
                        NEW rmi \in RM',
                        (rmState[rmi] = "committed")'
                 PROVE  (tmState = "committed")'
      BY DEF H_RMCommittedImpliesTMCommitted
    <2> QED
      BY DEF TypeOK,H_CommitMsgImpliesTMCommitted,RMRcvCommitMsgAction,RMRcvCommitMsg,H_RMCommittedImpliesTMCommitted
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** H_CommitSentImpliesRMsNotWorking
THEOREM L_12 == TypeOK /\ H_CommitMsgImpliesNoAbortMsg /\ H_RMAbortedAndPreparedImpliesTMAborted /\ H_TMKnowsPrepareImpliesRMWorking /\ H_CommitSentImpliesRMsNotWorking /\ Next => H_CommitSentImpliesRMsNotWorking'
  \* (H_CommitSentImpliesRMsNotWorking,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ H_CommitMsgImpliesNoAbortMsg /\ H_CommitSentImpliesRMsNotWorking /\ RMRcvAbortMsgAction => H_CommitSentImpliesRMsNotWorking' BY DEF TypeOK,H_CommitMsgImpliesNoAbortMsg,RMRcvAbortMsgAction,RMRcvAbortMsg,H_CommitSentImpliesRMsNotWorking
  \* (H_CommitSentImpliesRMsNotWorking,TMAbortAction)
  <1>2. TypeOK /\ H_CommitSentImpliesRMsNotWorking /\ TMAbortAction => H_CommitSentImpliesRMsNotWorking' BY DEF TypeOK,TMAbortAction,TMAbort,H_CommitSentImpliesRMsNotWorking
  \* (H_CommitSentImpliesRMsNotWorking,TMCommitAction)
  <1>3. TypeOK /\ H_RMAbortedAndPreparedImpliesTMAborted /\ H_TMKnowsPrepareImpliesRMWorking /\ H_CommitSentImpliesRMsNotWorking /\ TMCommitAction => H_CommitSentImpliesRMsNotWorking' BY DEF TypeOK,H_RMAbortedAndPreparedImpliesTMAborted,H_TMKnowsPrepareImpliesRMWorking,TMCommitAction,TMCommit,H_CommitSentImpliesRMsNotWorking
  \* (H_CommitSentImpliesRMsNotWorking,TMRcvPreparedAction)
  <1>4. TypeOK /\ H_CommitSentImpliesRMsNotWorking /\ TMRcvPreparedAction => H_CommitSentImpliesRMsNotWorking' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,H_CommitSentImpliesRMsNotWorking
  \* (H_CommitSentImpliesRMsNotWorking,RMPrepareAction)
  <1>5. TypeOK /\ H_CommitSentImpliesRMsNotWorking /\ RMPrepareAction => H_CommitSentImpliesRMsNotWorking' BY DEF TypeOK,RMPrepareAction,RMPrepare,H_CommitSentImpliesRMsNotWorking
  \* (H_CommitSentImpliesRMsNotWorking,RMChooseToAbortAction)
  <1>6. TypeOK /\ H_CommitSentImpliesRMsNotWorking /\ RMChooseToAbortAction => H_CommitSentImpliesRMsNotWorking' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,H_CommitSentImpliesRMsNotWorking
  \* (H_CommitSentImpliesRMsNotWorking,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ H_CommitSentImpliesRMsNotWorking /\ RMRcvCommitMsgAction => H_CommitSentImpliesRMsNotWorking' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,H_CommitSentImpliesRMsNotWorking
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** H_RMAbortedImpliesNoCommitMsg
THEOREM L_13 == TypeOK /\ H_CommitMsgImpliesNoAbortMsg /\ H_RMAbortedAndPreparedImpliesTMAborted /\ H_RMWorkingImpliesNoCommitMsg /\ H_RMAbortedImpliesNoCommitMsg /\ Next => H_RMAbortedImpliesNoCommitMsg'
  \* (H_RMAbortedImpliesNoCommitMsg,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ H_CommitMsgImpliesNoAbortMsg /\ H_RMAbortedImpliesNoCommitMsg /\ RMRcvAbortMsgAction => H_RMAbortedImpliesNoCommitMsg' BY DEF TypeOK,H_CommitMsgImpliesNoAbortMsg,RMRcvAbortMsgAction,RMRcvAbortMsg,H_RMAbortedImpliesNoCommitMsg
  \* (H_RMAbortedImpliesNoCommitMsg,TMAbortAction)
  <1>2. TypeOK /\ H_RMAbortedImpliesNoCommitMsg /\ TMAbortAction => H_RMAbortedImpliesNoCommitMsg' BY DEF TypeOK,TMAbortAction,TMAbort,H_RMAbortedImpliesNoCommitMsg
  \* (H_RMAbortedImpliesNoCommitMsg,TMCommitAction)
  <1>3. TypeOK /\ H_RMAbortedAndPreparedImpliesTMAborted /\ H_RMAbortedImpliesNoCommitMsg /\ TMCommitAction => H_RMAbortedImpliesNoCommitMsg' BY DEF TypeOK,H_RMAbortedAndPreparedImpliesTMAborted,TMCommitAction,TMCommit,H_RMAbortedImpliesNoCommitMsg
  \* (H_RMAbortedImpliesNoCommitMsg,TMRcvPreparedAction)
  <1>4. TypeOK /\ H_RMAbortedImpliesNoCommitMsg /\ TMRcvPreparedAction => H_RMAbortedImpliesNoCommitMsg' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,H_RMAbortedImpliesNoCommitMsg
  \* (H_RMAbortedImpliesNoCommitMsg,RMPrepareAction)
  <1>5. TypeOK /\ H_RMAbortedImpliesNoCommitMsg /\ RMPrepareAction => H_RMAbortedImpliesNoCommitMsg' BY DEF TypeOK,RMPrepareAction,RMPrepare,H_RMAbortedImpliesNoCommitMsg
  \* (H_RMAbortedImpliesNoCommitMsg,RMChooseToAbortAction)
  <1>6. TypeOK /\ H_RMWorkingImpliesNoCommitMsg /\ H_RMAbortedImpliesNoCommitMsg /\ RMChooseToAbortAction => H_RMAbortedImpliesNoCommitMsg' BY DEF TypeOK,H_RMWorkingImpliesNoCommitMsg,RMChooseToAbortAction,RMChooseToAbort,H_RMAbortedImpliesNoCommitMsg
  \* (H_RMAbortedImpliesNoCommitMsg,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ H_RMAbortedImpliesNoCommitMsg /\ RMRcvCommitMsgAction => H_RMAbortedImpliesNoCommitMsg' BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,H_RMAbortedImpliesNoCommitMsg
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** H_RMCommittedImpliesNoAbortMsg
THEOREM L_14 == TypeOK /\ H_RMCommittedImpliesTMCommitted /\ H_CommitMsgImpliesNoAbortMsg /\ H_RMCommittedImpliesNoAbortMsg /\ Next => H_RMCommittedImpliesNoAbortMsg'
  \* (H_RMCommittedImpliesNoAbortMsg,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ H_RMCommittedImpliesNoAbortMsg /\ RMRcvAbortMsgAction => H_RMCommittedImpliesNoAbortMsg' BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,H_RMCommittedImpliesNoAbortMsg
  \* (H_RMCommittedImpliesNoAbortMsg,TMAbortAction)
  <1>2. TypeOK /\ H_RMCommittedImpliesTMCommitted /\ H_RMCommittedImpliesNoAbortMsg /\ TMAbortAction => H_RMCommittedImpliesNoAbortMsg' BY DEF TypeOK,H_RMCommittedImpliesTMCommitted,TMAbortAction,TMAbort,H_RMCommittedImpliesNoAbortMsg
  \* (H_RMCommittedImpliesNoAbortMsg,TMCommitAction)
  <1>3. TypeOK /\ H_RMCommittedImpliesNoAbortMsg /\ TMCommitAction => H_RMCommittedImpliesNoAbortMsg' BY DEF TypeOK,TMCommitAction,TMCommit,H_RMCommittedImpliesNoAbortMsg
  \* (H_RMCommittedImpliesNoAbortMsg,TMRcvPreparedAction)
  <1>4. TypeOK /\ H_RMCommittedImpliesNoAbortMsg /\ TMRcvPreparedAction => H_RMCommittedImpliesNoAbortMsg' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,H_RMCommittedImpliesNoAbortMsg
  \* (H_RMCommittedImpliesNoAbortMsg,RMPrepareAction)
  <1>5. TypeOK /\ H_RMCommittedImpliesNoAbortMsg /\ RMPrepareAction => H_RMCommittedImpliesNoAbortMsg' BY DEF TypeOK,RMPrepareAction,RMPrepare,H_RMCommittedImpliesNoAbortMsg
  \* (H_RMCommittedImpliesNoAbortMsg,RMChooseToAbortAction)
  <1>6. TypeOK /\ H_RMCommittedImpliesNoAbortMsg /\ RMChooseToAbortAction => H_RMCommittedImpliesNoAbortMsg' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,H_RMCommittedImpliesNoAbortMsg
  \* (H_RMCommittedImpliesNoAbortMsg,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ H_CommitMsgImpliesNoAbortMsg /\ H_RMCommittedImpliesNoAbortMsg /\ RMRcvCommitMsgAction => H_RMCommittedImpliesNoAbortMsg' BY DEF TypeOK,H_CommitMsgImpliesNoAbortMsg,RMRcvCommitMsgAction,RMRcvCommitMsg,H_RMCommittedImpliesNoAbortMsg
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** H_RMCommittedImpliesNoRMsWorking
THEOREM L_15 == TypeOK /\ H_RMCommittedImpliesNoAbortMsg /\ H_CommitSentImpliesRMsNotWorking /\ H_RMCommittedImpliesNoRMsWorking /\ Next => H_RMCommittedImpliesNoRMsWorking'
  \* (H_RMCommittedImpliesNoRMsWorking,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ H_RMCommittedImpliesNoAbortMsg /\ H_RMCommittedImpliesNoRMsWorking /\ RMRcvAbortMsgAction => H_RMCommittedImpliesNoRMsWorking' BY DEF TypeOK,H_RMCommittedImpliesNoAbortMsg,RMRcvAbortMsgAction,RMRcvAbortMsg,H_RMCommittedImpliesNoRMsWorking
  \* (H_RMCommittedImpliesNoRMsWorking,TMAbortAction)
  <1>2. TypeOK /\ H_RMCommittedImpliesNoRMsWorking /\ TMAbortAction => H_RMCommittedImpliesNoRMsWorking' BY DEF TypeOK,TMAbortAction,TMAbort,H_RMCommittedImpliesNoRMsWorking
  \* (H_RMCommittedImpliesNoRMsWorking,TMCommitAction)
  <1>3. TypeOK /\ H_RMCommittedImpliesNoRMsWorking /\ TMCommitAction => H_RMCommittedImpliesNoRMsWorking' BY DEF TypeOK,TMCommitAction,TMCommit,H_RMCommittedImpliesNoRMsWorking
  \* (H_RMCommittedImpliesNoRMsWorking,TMRcvPreparedAction)
  <1>4. TypeOK /\ H_RMCommittedImpliesNoRMsWorking /\ TMRcvPreparedAction => H_RMCommittedImpliesNoRMsWorking' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,H_RMCommittedImpliesNoRMsWorking
  \* (H_RMCommittedImpliesNoRMsWorking,RMPrepareAction)
  <1>5. TypeOK /\ H_RMCommittedImpliesNoRMsWorking /\ RMPrepareAction => H_RMCommittedImpliesNoRMsWorking' BY DEF TypeOK,RMPrepareAction,RMPrepare,H_RMCommittedImpliesNoRMsWorking
  \* (H_RMCommittedImpliesNoRMsWorking,RMChooseToAbortAction)
  <1>6. TypeOK /\ H_RMCommittedImpliesNoRMsWorking /\ RMChooseToAbortAction => H_RMCommittedImpliesNoRMsWorking' BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,H_RMCommittedImpliesNoRMsWorking
  \* (H_RMCommittedImpliesNoRMsWorking,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ H_CommitSentImpliesRMsNotWorking /\ H_RMCommittedImpliesNoRMsWorking /\ RMRcvCommitMsgAction => H_RMCommittedImpliesNoRMsWorking' BY DEF TypeOK,H_CommitSentImpliesRMsNotWorking,RMRcvCommitMsgAction,RMRcvCommitMsg,H_RMCommittedImpliesNoRMsWorking
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\* (ROOT SAFETY PROP)
\*** H_TCConsistent
THEOREM L_16 == TypeOK /\ H_RMCommittedImpliesNoAbortMsg /\ H_RMCommittedImpliesNoRMsWorking /\ H_RMAbortedImpliesNoCommitMsg /\ H_TCConsistent /\ Next => H_TCConsistent'
  \* (H_TCConsistent,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ H_RMCommittedImpliesNoAbortMsg /\ H_TCConsistent /\ RMRcvAbortMsgAction => H_TCConsistent' BY DEF TypeOK,H_RMCommittedImpliesNoAbortMsg,RMRcvAbortMsgAction,RMRcvAbortMsg,H_TCConsistent
  \* (H_TCConsistent,TMAbortAction)
  <1>2. TypeOK /\ H_TCConsistent /\ TMAbortAction => H_TCConsistent' BY DEF TypeOK,TMAbortAction,TMAbort,H_TCConsistent
  \* (H_TCConsistent,TMCommitAction)
  <1>3. TypeOK /\ H_TCConsistent /\ TMCommitAction => H_TCConsistent' BY DEF TypeOK,TMCommitAction,TMCommit,H_TCConsistent
  \* (H_TCConsistent,TMRcvPreparedAction)
  <1>4. TypeOK /\ H_TCConsistent /\ TMRcvPreparedAction => H_TCConsistent' BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,H_TCConsistent
  \* (H_TCConsistent,RMPrepareAction)
  <1>5. TypeOK /\ H_TCConsistent /\ RMPrepareAction => H_TCConsistent' BY DEF TypeOK,RMPrepareAction,RMPrepare,H_TCConsistent
  \* (H_TCConsistent,RMChooseToAbortAction)
  <1>6. TypeOK /\ H_RMCommittedImpliesNoRMsWorking /\ H_TCConsistent /\ RMChooseToAbortAction => H_TCConsistent' BY DEF TypeOK,H_RMCommittedImpliesNoRMsWorking,RMChooseToAbortAction,RMChooseToAbort,H_TCConsistent
  \* (H_TCConsistent,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ H_RMAbortedImpliesNoCommitMsg /\ H_TCConsistent /\ RMRcvCommitMsgAction => H_TCConsistent' BY DEF TypeOK,H_RMAbortedImpliesNoCommitMsg,RMRcvCommitMsgAction,RMRcvCommitMsg,H_TCConsistent
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => H_AbortMsgImpliesTMAborted BY DEF Init, H_AbortMsgImpliesTMAborted, IndGlobal
    <1>2. Init => H_RMSentPrepareImpliesNotWorking BY DEF Init, H_RMSentPrepareImpliesNotWorking, IndGlobal
    <1>3. Init => H_RMWorkingImpliesNotPrepared BY DEF Init, H_RMWorkingImpliesNotPrepared, IndGlobal
    <1>4. Init => H_InitNoAbortMsg BY DEF Init, H_InitNoAbortMsg, IndGlobal
    <1>5. Init => H_InitNoCommitMsg BY DEF Init, H_InitNoCommitMsg, IndGlobal
    <1>6. Init => H_CommitMsgImpliesTMCommitted BY DEF Init, H_CommitMsgImpliesTMCommitted, IndGlobal
    <1>7. Init => H_TMKnowsPrepareImpliesRMWorking BY DEF Init, H_TMKnowsPrepareImpliesRMWorking, IndGlobal
    <1>8. Init => H_RMAbortedAndPreparedImpliesTMAborted BY DEF Init, H_RMAbortedAndPreparedImpliesTMAborted, IndGlobal
    <1>9. Init => H_RMWorkingImpliesNoCommitMsg BY DEF Init, H_RMWorkingImpliesNoCommitMsg, IndGlobal
    <1>10. Init => H_CommitMsgImpliesNoAbortMsg BY DEF Init, H_CommitMsgImpliesNoAbortMsg, IndGlobal
    <1>11. Init => H_RMCommittedImpliesTMCommitted BY DEF Init, H_RMCommittedImpliesTMCommitted, IndGlobal
    <1>12. Init => H_CommitSentImpliesRMsNotWorking BY DEF Init, H_CommitSentImpliesRMsNotWorking, IndGlobal
    <1>13. Init => H_RMAbortedImpliesNoCommitMsg BY DEF Init, H_RMAbortedImpliesNoCommitMsg, IndGlobal
    <1>14. Init => H_RMCommittedImpliesNoAbortMsg BY DEF Init, H_RMCommittedImpliesNoAbortMsg, IndGlobal
    <1>15. Init => H_RMCommittedImpliesNoRMsWorking BY DEF Init, H_RMCommittedImpliesNoRMsWorking, IndGlobal
    <1>16. Init => H_TCConsistent BY DEF Init, H_TCConsistent, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14,<1>15,<1>16 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13,L_14,L_15,L_16 DEF Next, IndGlobal

====
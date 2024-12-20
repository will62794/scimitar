------------------------------- MODULE Hermes_IndProofs -------------------------------
EXTENDS Hermes, TLAPS, FiniteSetTheorems

\* \* Proof Graph Stats
\* \* ==================
\* \* seed: 8
\* \* num proof graph nodes: 26
\* \* num proof obligations: 234
\* Safety == HConsistent
\* Inv2345_R0_0_I2 == \A VARI \in H_NODES : \A VARMVALI \in msgsVAL : ~(VARI \in aliveNodes) \/ (~(greaterTS(VARMVALI.version, VARMVALI.tieBreaker, nodeTS[VARI].version, nodeTS[VARI].tieBreaker)))
\* Inv3096_R0_0_I2 == \A VARI \in H_NODES : \A VARJ \in H_NODES : ~(nodeTS[VARI].tieBreaker = VARJ) \/ (~(nodeTS[VARI].version > nodeTS[VARJ].version))
\* Inv14828_R0_0_I2 == \A VARI \in H_NODES : \A VARJ \in H_NODES : ~(greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(nodeTS[VARI].tieBreaker = VARJ) \/ (~(nodeTS[VARI].tieBreaker > nodeTS[VARJ].tieBreaker)))
\* Inv4085_R0_0_I2 == \A VARI \in H_NODES : \A VARJ \in H_NODES : (greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(VARI \in aliveNodes) \/ (~(nodeState[VARJ] = "valid")))
\* Inv13944_R0_0_I2 == \A VARI \in H_NODES : \A VARJ \in H_NODES : ~(VARJ \in aliveNodes) \/ (~(nodeState[VARI] = "valid")) \/ (~(nodeTS[VARI].version > nodeTS[VARJ].version))
\* Inv13951_R0_0_I2 == \A VARI \in H_NODES : ~(VARI \in aliveNodes) \/ (~(nodeState[VARI] = "invalid_write") \/ (~(nodeTS[VARI].tieBreaker = VARI)))
\* Inv2018_R0_0_I2 == \A VARI \in H_NODES : (nodeTS[VARI].tieBreaker = VARI) \/ (~(nodeState[VARI] = "write"))
\* Inv2701_R0_0_I2 == \A VARI \in H_NODES : ~(nodeState[VARI] = "invalid") \/ (~(nodeTS[VARI].tieBreaker = VARI))
\* Inv4_R0_1_I2 == \A VARI \in H_NODES : \A VARJ \in H_NODES : (VARI \in aliveNodes) \/ (~(VARI \in nodeRcvedAcks[VARJ]))
\* Inv10494_R0_1_I2 == \A VARI \in H_NODES : \A VARJ \in H_NODES : ~(VARJ \in nodeRcvedAcks[VARI]) \/ (~(nodeState[VARI] \in {"write", "replay"}) \/ (~(nodeTS[VARI].version > nodeTS[VARJ].version)))
\* Inv4836_R0_1_I2 == \A VARI \in H_NODES : (nodeState[VARI] \in {"write", "replay"}) \/ (~(nodeState[VARI] = "invalid")) \/ (~(nodeTS[VARI].tieBreaker = VARI))
\* Inv548_R0_1_I2 == \A VARI \in H_NODES : ~(nodeState[VARI] = "invalid_write") \/ (~(nodeTS[VARI].tieBreaker = VARI))
\* Inv5_R0_1_I2 == \A VARI \in H_NODES : \A VARJ \in H_NODES : (VARI \in aliveNodes) \/ (~(VARJ \in nodeRcvedAcks[VARI]))
\* Inv7971_R0_1_I2 == \A VARI \in H_NODES : \A VARJ \in H_NODES : ~(VARI \in aliveNodes) \/ (~(nodeState[VARJ] = "valid") \/ (~(nodeTS[VARI].version < nodeTS[VARJ].version)))
\* Inv890_R0_1_I2 == \A VARI \in H_NODES : \A VARJ \in H_NODES : (greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(nodeState[VARJ] = "valid")) \/ (~(receivedAllAcks(VARI) /\ nodeRcvedAcks = nodeRcvedAcks))
\* Inv618_R0_1_I2 == \A VARI \in H_NODES : \A VARJ \in H_NODES : (greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(nodeState[VARJ] = "write")) \/ (~(VARI \in nodeRcvedAcks[VARJ]))
\* Inv3025_R1_0_I2 == \A VARI \in H_NODES : \A VARJ \in H_NODES : (greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(VARI \in nodeRcvedAcks[VARJ]) \/ (~(nodeState[VARJ] \in {"write", "replay"})))
\* Inv29_R2_0_I1 == \A VARMINVI \in msgsINV : ~(VARMINVI.epochID > epochID)
\* Inv3029_R2_0_I1 == \A VARI \in H_NODES : \A VARMINVI \in msgsINV : ~(VARMINVI.tieBreaker = VARI) \/ (~(greaterTS(VARMINVI.version, VARMINVI.tieBreaker, nodeTS[VARI].version, nodeTS[VARI].tieBreaker)))
\* Inv627_R9_0_I2 == \A VARI \in H_NODES : (nodeLastWriteTS[VARI].tieBreaker = VARI) \/ ((nodeState[VARI] \in {"valid", "invalid", "replay"}))
\* Inv927_R9_0_I2 == \A VARJ \in H_NODES : \A VARMACKI \in msgsACK : (VARJ \in aliveNodes) \/ (~(VARMACKI.epochID = epochID) \/ (~(VARMACKI.sender = VARJ)))
\* Inv1666_R10_0_I1 == \A VARI \in H_NODES : (nodeTS[VARI] = nodeLastWriteTS[VARI]) \/ (~(nodeTS[VARI].tieBreaker = VARI))
\* Inv62_R15_1_I1 == \A VARI \in H_NODES : \A VARJ \in H_NODES : \A VARMVALI \in msgsVAL : ~(VARJ \in nodeRcvedAcks[VARI]) \/ (~(greaterTS(VARMVALI.version, VARMVALI.tieBreaker, nodeTS[VARI].version, nodeTS[VARI].tieBreaker)))
\* Inv28_R17_0_I1 == \A VARI \in H_NODES : (nodeTS[VARI] = nodeLastWriteTS[VARI]) \/ (~(nodeState[VARI] = "replay"))
\* Inv1_R21_0_I0 == \A VARMACKI \in msgsACK : ~(VARMACKI.epochID > epochID)

\* IndGlobal == 
\*   /\ TypeOK
\*   /\ Safety
\*   /\ Inv2345_R0_0_I2
\*   /\ Inv10494_R0_1_I2
\*   /\ Inv627_R9_0_I2
\*   /\ Inv5_R0_1_I2
\*   /\ Inv3096_R0_0_I2
\*   /\ Inv29_R2_0_I1
\*   /\ Inv14828_R0_0_I2
\*   /\ Inv3029_R2_0_I1
\*   /\ Inv548_R0_1_I2
\*   /\ Inv2701_R0_0_I2
\*   /\ Inv4085_R0_0_I2
\*   /\ Inv3025_R1_0_I2
\*   /\ Inv1666_R10_0_I1
\*   /\ Inv28_R17_0_I1
\*   /\ Inv2018_R0_0_I2
\*   /\ Inv4_R0_1_I2
\*   /\ Inv927_R9_0_I2
\*   /\ Inv1_R21_0_I0
\*   /\ Inv7971_R0_1_I2
\*   /\ Inv13944_R0_0_I2
\*   /\ Inv13951_R0_0_I2
\*   /\ Inv4836_R0_1_I2
\*   /\ Inv890_R0_1_I2
\*   /\ Inv62_R15_1_I1
\*   /\ Inv618_R0_1_I2


\* \* mean in-degree: 2.8846153846153846
\* \* median in-degree: 2
\* \* max in-degree: 19
\* \* min in-degree: 0
\* \* mean variable slice size: 0


\* ASSUME A1 == IsFiniteSet(H_NODES) /\ H_NODES \subseteq Nat /\ H_NODES # {} /\ H_MAX_VERSION \in Nat /\ \E k \in H_NODES : \A m \in H_NODES : k =< m
\* USE A1
\* USE DEF INVMessage, ACKMessage, VALMessage


\* \*** TypeOK
\* THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
\*   \* (TypeOK,HRcvInvAction)
\*   <1>1. TypeOK /\ TypeOK /\ HRcvInvAction => TypeOK' 
\*     <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ HRcvInvAction
\*                  PROVE  TypeOK'
\*       OBVIOUS
\*     <2>1. (msgsINV \subseteq INVMessage)'
\*       BY DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
\*     <2>2. (msgsVAL \subseteq VALMessage)'
\*       BY DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
\*     <2>3. (msgsACK \subseteq ACKMessage)'
\*       BY FS_Subset DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK, ACKMessage, INVMessage, greaterTS
\*     <2>4. (nodeRcvedAcks \in [H_NODES -> SUBSET H_NODES])'
\*       BY DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
\*     <2>5. (\A n \in H_NODES: nodeRcvedAcks[n] \subseteq (H_NODES \ {n}))'
\*       BY DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
\*     <2>6. (nodeLastWriter  \in [H_NODES -> H_NODES])'
\*       BY DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
\*     <2>7. (nodeLastWriteTS \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]])'
\*       BY DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
\*     <2>8. (nodeTS          \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]])'
\*       BY DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
\*     <2>9. (nodeState       \in [H_NODES -> {"valid", "invalid", "invalid_write", "write", "replay"}])'
\*       BY DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
\*     <2>10. (aliveNodes      \in SUBSET H_NODES)'
\*       BY DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
\*     <2>11. (epochID         \in Nat)'
\*       BY DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
\*     <2>12. (nodeWriteEpochID \in [H_NODES -> Nat])'
\*       BY DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
\*     <2>13. QED
\*       BY <2>1, <2>10, <2>11, <2>12, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
\*   \* (TypeOK,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ TypeOK /\ HRcvInvNewerAction => TypeOK' 
\*     <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ HRcvInvNewerAction
\*                  PROVE  TypeOK'
\*       OBVIOUS
\*     <2>1. (msgsINV \subseteq INVMessage)'
\*       BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
\*     <2>2. (msgsVAL \subseteq VALMessage)'
\*       BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
\*     <2>3. (msgsACK \subseteq ACKMessage)'
\*       BY FS_Subset, FS_Singleton DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK, ACKMessage, INVMessage, greaterTS
\*     <2>4. (nodeRcvedAcks \in [H_NODES -> SUBSET H_NODES])'
\*       BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
\*     <2>5. (\A n \in H_NODES: nodeRcvedAcks[n] \subseteq (H_NODES \ {n}))'
\*       BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
\*     <2>6. (nodeLastWriter  \in [H_NODES -> H_NODES])'
\*       BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
\*     <2>7. (nodeLastWriteTS \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]])'
\*       BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
\*     <2>8. (nodeTS          \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]])'
\*       BY FS_Subset, FS_Singleton DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
\*     <2>9. (nodeState       \in [H_NODES -> {"valid", "invalid", "invalid_write", "write", "replay"}])'
\*       BY  FS_Subset, FS_Singleton, FS_Difference DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK, greaterTS
\*     <2>10. (aliveNodes      \in SUBSET H_NODES)'
\*       BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
\*     <2>11. (epochID         \in Nat)'
\*       BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
\*     <2>12. (nodeWriteEpochID \in [H_NODES -> Nat])'
\*       BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
\*     <2>13. QED
\*       BY <2>1, <2>10, <2>11, <2>12, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
\*   \* (TypeOK,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ TypeOK /\ HFollowerWriteReplayAction => TypeOK' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,TypeOK
\*   \* (TypeOK,HRcvValAction)
\*   <1>4. TypeOK /\ TypeOK /\ HRcvValAction => TypeOK' BY DEF TypeOK,HRcvValAction,HRcvVal,TypeOK
\*   \* (TypeOK,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ TypeOK /\ HCoordWriteReplayAction => TypeOK' 
\*     <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ HCoordWriteReplayAction
\*                  PROVE  TypeOK'
\*       OBVIOUS
\*     <2>1. (msgsINV \subseteq INVMessage)'
\*       BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,TypeOK, INVMessage
\*     <2>2. (msgsVAL \subseteq VALMessage)'
\*       BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,TypeOK
\*     <2>3. (msgsACK \subseteq ACKMessage)'
\*       BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,TypeOK
\*     <2>4. (nodeRcvedAcks \in [H_NODES -> SUBSET H_NODES])'
\*       BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,TypeOK
\*     <2>5. (\A n \in H_NODES: nodeRcvedAcks[n] \subseteq (H_NODES \ {n}))'
\*       BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,TypeOK
\*     <2>6. (nodeLastWriter  \in [H_NODES -> H_NODES])'
\*       BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,TypeOK
\*     <2>7. (nodeLastWriteTS \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]])'
\*       BY FS_Subset, FS_Singleton DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,TypeOK
\*     <2>8. (nodeTS          \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]])'
\*       BY FS_Subset, FS_Singleton DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,TypeOK, receivedAllAcks
\*     <2>9. (nodeState       \in [H_NODES -> {"valid", "invalid", "invalid_write", "write", "replay"}])'
\*       BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,TypeOK
\*     <2>10. (aliveNodes      \in SUBSET H_NODES)'
\*       BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,TypeOK
\*     <2>11. (epochID         \in Nat)'
\*       BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,TypeOK
\*     <2>12. (nodeWriteEpochID \in [H_NODES -> Nat])'
\*       BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,TypeOK
\*     <2>13. QED
\*       BY <2>1, <2>10, <2>11, <2>12, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
\*   \* (TypeOK,HWriteAction)
\*   <1>6. TypeOK /\ TypeOK /\ HWriteAction => TypeOK' BY DEF TypeOK,HWriteAction,HWrite,TypeOK
\*   \* (TypeOK,HRcvAckAction)
\*   <1>7. TypeOK /\ TypeOK /\ HRcvAckAction => TypeOK' BY DEF TypeOK,HRcvAckAction,HRcvAck,TypeOK
\*   \* (TypeOK,HSendValsAction)
\*   <1>8. TypeOK /\ TypeOK /\ HSendValsAction => TypeOK' BY DEF TypeOK,HSendValsAction,HSendVals,TypeOK,receivedAllAcks,VALMessage
\*   \* (TypeOK,NodeFailureAction)
\*   <1>9. TypeOK /\ TypeOK /\ NodeFailureAction => TypeOK' BY DEF TypeOK,NodeFailureAction,NodeFailure,TypeOK
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*USE DEF greaterOrEqualTS, greaterTS, equalTS
\* \* (ROOT SAFETY PROP)
\* \*** Safety
\* THEOREM L_1 == TypeOK /\ Inv2345_R0_0_I2 /\ Inv3096_R0_0_I2 /\ Inv14828_R0_0_I2 /\ Inv4085_R0_0_I2 /\ Inv13944_R0_0_I2 /\ Inv13951_R0_0_I2 /\ Inv2018_R0_0_I2 /\ Inv2701_R0_0_I2 /\ Inv4_R0_1_I2 /\ Inv3096_R0_0_I2 /\ Inv10494_R0_1_I2 /\ Inv2018_R0_0_I2 /\ Inv4836_R0_1_I2 /\ Inv14828_R0_0_I2 /\ Inv548_R0_1_I2 /\ Inv5_R0_1_I2 /\ Inv7971_R0_1_I2 /\ Inv890_R0_1_I2 /\ Inv618_R0_1_I2 /\ Safety /\ Next => Safety'
\*   \* (Safety,HRcvInvAction)
\*   <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
\*   <1>1. TypeOK /\ Safety /\ HRcvInvAction => Safety' BY DEF TypeOK,HRcvInvAction,HRcvInv,Safety,HConsistent
\*   \* (Safety,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Safety /\ HRcvInvNewerAction => Safety' BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Safety,HConsistent
\*   \* (Safety,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Safety /\ HFollowerWriteReplayAction => Safety' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Safety,HConsistent
\*   \* (Safety,HRcvValAction)
\*   <1>4. TypeOK /\ Inv2345_R0_0_I2 /\ Inv3096_R0_0_I2 /\ Inv14828_R0_0_I2 /\ Inv4085_R0_0_I2 /\ Inv13944_R0_0_I2 /\ Inv13951_R0_0_I2 /\ Inv2018_R0_0_I2 /\ Inv2701_R0_0_I2 /\ Safety /\ HRcvValAction => Safety' BY DEF TypeOK,Inv2345_R0_0_I2,Inv3096_R0_0_I2,Inv14828_R0_0_I2,Inv4085_R0_0_I2,Inv13944_R0_0_I2,Inv13951_R0_0_I2,Inv2018_R0_0_I2,Inv2701_R0_0_I2,HRcvValAction,HRcvVal,Safety,HConsistent
\*   \* (Safety,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Safety /\ HCoordWriteReplayAction => Safety' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Safety,HConsistent
\*   \* (Safety,HWriteAction)
\*   <1>6. TypeOK /\ Safety /\ HWriteAction => Safety' BY DEF TypeOK,HWriteAction,HWrite,Safety,HConsistent
\*   \* (Safety,HRcvAckAction)
\*   <1>7. TypeOK /\ Safety /\ HRcvAckAction => Safety' BY DEF TypeOK,HRcvAckAction,HRcvAck,Safety,HConsistent
\*   \* (Safety,HSendValsAction)
\*   <1>8. TypeOK /\ Inv4_R0_1_I2 /\ Inv3096_R0_0_I2 /\ Inv10494_R0_1_I2 /\ Inv2018_R0_0_I2 /\ Inv4836_R0_1_I2 /\ Inv14828_R0_0_I2 /\ Inv548_R0_1_I2 /\ Inv5_R0_1_I2 /\ Inv7971_R0_1_I2 /\ Inv890_R0_1_I2 /\ Inv618_R0_1_I2 /\ Safety /\ HSendValsAction => Safety' 
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv4_R0_1_I2,
\*                         Inv3096_R0_0_I2,
\*                         Inv10494_R0_1_I2,
\*                         Inv2018_R0_0_I2,
\*                         Inv4836_R0_1_I2,
\*                         Inv14828_R0_0_I2,
\*                         Inv548_R0_1_I2,
\*                         Inv5_R0_1_I2,
\*                         Inv7971_R0_1_I2,
\*                         Inv890_R0_1_I2,
\*                         Inv618_R0_1_I2,
\*                         Safety,
\*                         TRUE,
\*                         NEW n \in aliveNodes,
\*                         HSendVals(n)
\*                  PROVE  Safety'
\*       BY DEF HSendValsAction
\*     <2> QED
\*       BY FS_Subset, FS_Singleton, FS_Difference DEF TypeOK,Inv4_R0_1_I2,Inv3096_R0_0_I2,Inv10494_R0_1_I2,Inv2018_R0_0_I2,Inv4836_R0_1_I2,Inv14828_R0_0_I2,Inv548_R0_1_I2,Inv5_R0_1_I2,Inv7971_R0_1_I2,Inv890_R0_1_I2,Inv618_R0_1_I2,HSendValsAction,HSendVals,Safety,receivedAllAcks,VALMessage,HConsistent
\*   \* (Safety,NodeFailureAction)
\*   <1>9. TypeOK /\ Safety /\ NodeFailureAction => Safety' BY DEF TypeOK,NodeFailureAction,NodeFailure,Safety,HConsistent
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv2345_R0_0_I2
\* THEOREM L_2 == TypeOK /\ Inv10494_R0_1_I2 /\ Inv4_R0_1_I2 /\ Inv3096_R0_0_I2 /\ Inv3025_R1_0_I2 /\ Inv2018_R0_0_I2 /\ Inv7971_R0_1_I2 /\ Inv2345_R0_0_I2 /\ Next => Inv2345_R0_0_I2'
\*     <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
  
\*   \* (Inv2345_R0_0_I2,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv2345_R0_0_I2 /\ HRcvInvAction => Inv2345_R0_0_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv2345_R0_0_I2
\*   \* (Inv2345_R0_0_I2,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv2345_R0_0_I2 /\ HRcvInvNewerAction => Inv2345_R0_0_I2' 
\*     <2> SUFFICES ASSUME TypeOK /\ Inv2345_R0_0_I2 /\ HRcvInvNewerAction,
\*                         NEW VARI \in H_NODES',
\*                         NEW VARMVALI \in msgsVAL'
\*                  PROVE  (~(VARI \in aliveNodes) \/ (~(greaterTS(VARMVALI.version, VARMVALI.tieBreaker, nodeTS[VARI].version, nodeTS[VARI].tieBreaker))))'
\*       BY DEF Inv2345_R0_0_I2
\*     <2> QED
\*       BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv2345_R0_0_I2
\*   \* (Inv2345_R0_0_I2,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv2345_R0_0_I2 /\ HFollowerWriteReplayAction => Inv2345_R0_0_I2' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv2345_R0_0_I2
\*   \* (Inv2345_R0_0_I2,HRcvValAction)
\*   <1>4. TypeOK /\ Inv2345_R0_0_I2 /\ HRcvValAction => Inv2345_R0_0_I2' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv2345_R0_0_I2
\*   \* (Inv2345_R0_0_I2,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv2345_R0_0_I2 /\ HCoordWriteReplayAction => Inv2345_R0_0_I2' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv2345_R0_0_I2
\*   \* (Inv2345_R0_0_I2,HWriteAction)
\*   <1>6. TypeOK /\ Inv2345_R0_0_I2 /\ HWriteAction => Inv2345_R0_0_I2' 
\*     <2> SUFFICES ASSUME TypeOK /\ Inv2345_R0_0_I2 /\ HWriteAction,
\*                         NEW VARI \in H_NODES',
\*                         NEW VARMVALI \in msgsVAL'
\*                  PROVE  (~(VARI \in aliveNodes) \/ (~(greaterTS(VARMVALI.version, VARMVALI.tieBreaker, nodeTS[VARI].version, nodeTS[VARI].tieBreaker))))'
\*       BY DEF Inv2345_R0_0_I2
\*     <2> QED
\*       BY DEF TypeOK,HWriteAction,HWrite,Inv2345_R0_0_I2,VALMessage
\*   \* (Inv2345_R0_0_I2,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv2345_R0_0_I2 /\ HRcvAckAction => Inv2345_R0_0_I2' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv2345_R0_0_I2
\*   \* (Inv2345_R0_0_I2,HSendValsAction)
\*   <1>8. TypeOK /\ Inv10494_R0_1_I2 /\ Inv4_R0_1_I2 /\ Inv3096_R0_0_I2 /\ Inv3025_R1_0_I2 /\ Inv2018_R0_0_I2 /\ Inv7971_R0_1_I2 /\ Inv2345_R0_0_I2 /\ HSendValsAction => Inv2345_R0_0_I2' BY DEF TypeOK,Inv10494_R0_1_I2,Inv4_R0_1_I2,Inv3096_R0_0_I2,Inv3025_R1_0_I2,Inv2018_R0_0_I2,Inv7971_R0_1_I2,HSendValsAction,HSendVals,Inv2345_R0_0_I2,receivedAllAcks,VALMessage
\*   \* (Inv2345_R0_0_I2,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv2345_R0_0_I2 /\ NodeFailureAction => Inv2345_R0_0_I2' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv2345_R0_0_I2
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv10494_R0_1_I2
\* THEOREM L_3 == TypeOK /\ Inv627_R9_0_I2 /\ Inv5_R0_1_I2 /\ Inv3096_R0_0_I2 /\ Inv1666_R10_0_I1 /\ Inv10494_R0_1_I2 /\ Next => Inv10494_R0_1_I2'
\*     <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
  
\*   \* (Inv10494_R0_1_I2,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv10494_R0_1_I2 /\ HRcvInvAction => Inv10494_R0_1_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv10494_R0_1_I2
\*   \* (Inv10494_R0_1_I2,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv10494_R0_1_I2 /\ HRcvInvNewerAction => Inv10494_R0_1_I2' 
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv10494_R0_1_I2,
\*                         TRUE,
\*                         NEW n \in aliveNodes, NEW m \in msgsINV,
\*                         n \in aliveNodes,
\*                         m \in msgsINV,
\*                         m.type     = "INV",
\*                         m.epochID  = epochID,
\*                         m.sender  # n,
\*                         msgsACK' = msgsACK \cup {[type       |-> "ACK",
\*                                                   sender     |-> n,   
\*                                                   epochID    |-> epochID,
\*                                                   version    |-> m.version,
\*                                                   tieBreaker |-> m.tieBreaker]},
\*                         nodeLastWriter' = [nodeLastWriter EXCEPT ![n] = m.sender],
\*                         nodeTS' = [nodeTS EXCEPT ![n].version    = m.version, ![n].tieBreaker = m.tieBreaker],
\*                         IF nodeState[n] \in {"valid", "invalid", "replay"}
\*                              THEN 
\*                              nodeState' = [nodeState EXCEPT ![n] = "invalid"]
\*                              ELSE 
\*                              nodeState' = [nodeState EXCEPT ![n] = "invalid_write"],
\*                         UNCHANGED <<nodeLastWriteTS, aliveNodes, nodeRcvedAcks, epochID, nodeWriteEpochID, msgsVAL, msgsINV>>,
\*                         NEW VARI \in H_NODES',
\*                         NEW VARJ \in H_NODES',
\*                         greaterTS(m.version, m.tieBreaker, nodeTS[n].version, nodeTS[n].tieBreaker)
\*                  PROVE  (~(VARJ \in nodeRcvedAcks[VARI]) \/ (~(nodeState[VARI] \in {"write", "replay"}) \/ (~(nodeTS[VARI].version > nodeTS[VARJ].version))))'
\*       BY DEF HRcvInvNewer, HRcvInvNewerAction, Inv10494_R0_1_I2
\*     <2>1. CASE (m.version) > (nodeTS[n].version)
\*       BY <2>1 DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv10494_R0_1_I2
\*     <2>2. CASE /\   (m.version) = (nodeTS[n].version)
\*                /\  (m.tieBreaker) > (nodeTS[n].tieBreaker)
\*       BY <2>2 DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv10494_R0_1_I2
\*     <2>3. QED
\*       BY <2>1, <2>2 DEF greaterTS
\*   \* (Inv10494_R0_1_I2,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv10494_R0_1_I2 /\ HFollowerWriteReplayAction => Inv10494_R0_1_I2' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv10494_R0_1_I2
\*   \* (Inv10494_R0_1_I2,HRcvValAction)
\*   <1>4. TypeOK /\ Inv10494_R0_1_I2 /\ HRcvValAction => Inv10494_R0_1_I2' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv10494_R0_1_I2
\*   \* (Inv10494_R0_1_I2,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv10494_R0_1_I2 /\ HCoordWriteReplayAction => Inv10494_R0_1_I2' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv10494_R0_1_I2
\*   \* (Inv10494_R0_1_I2,HWriteAction)
\*   <1>6. TypeOK /\ Inv10494_R0_1_I2 /\ HWriteAction => Inv10494_R0_1_I2' BY DEF TypeOK,HWriteAction,HWrite,Inv10494_R0_1_I2
\*   \* (Inv10494_R0_1_I2,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv627_R9_0_I2 /\ Inv5_R0_1_I2 /\ Inv3096_R0_0_I2 /\ Inv1666_R10_0_I1 /\ Inv10494_R0_1_I2 /\ HRcvAckAction => Inv10494_R0_1_I2' BY DEF TypeOK,Inv627_R9_0_I2,Inv5_R0_1_I2,Inv3096_R0_0_I2,Inv1666_R10_0_I1,HRcvAckAction,HRcvAck,Inv10494_R0_1_I2
\*   \* (Inv10494_R0_1_I2,HSendValsAction)
\*   <1>8. TypeOK /\ Inv10494_R0_1_I2 /\ HSendValsAction => Inv10494_R0_1_I2' BY DEF TypeOK,HSendValsAction,HSendVals,Inv10494_R0_1_I2,receivedAllAcks,VALMessage
\*   \* (Inv10494_R0_1_I2,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv10494_R0_1_I2 /\ NodeFailureAction => Inv10494_R0_1_I2' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv10494_R0_1_I2
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv627_R9_0_I2
\* THEOREM L_4 == TypeOK /\ Inv627_R9_0_I2 /\ Next => Inv627_R9_0_I2'
\*     <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
 
\*   \* (Inv627_R9_0_I2,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv627_R9_0_I2 /\ HRcvInvAction => Inv627_R9_0_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv627_R9_0_I2
\*   \* (Inv627_R9_0_I2,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv627_R9_0_I2 /\ HRcvInvNewerAction => Inv627_R9_0_I2' 
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv627_R9_0_I2,
\*                         TRUE,
\*                         NEW n \in aliveNodes, NEW m \in msgsINV,
\*                         n \in aliveNodes,
\*                         m \in msgsINV,
\*                         m.type     = "INV",
\*                         m.epochID  = epochID,
\*                         m.sender  # n,
\*                         msgsACK' = msgsACK \cup {[type       |-> "ACK",
\*                                                   sender     |-> n,   
\*                                                   epochID    |-> epochID,
\*                                                   version    |-> m.version,
\*                                                   tieBreaker |-> m.tieBreaker]},
\*                         nodeLastWriter' = [nodeLastWriter EXCEPT ![n] = m.sender],
\*                         nodeTS' = [nodeTS EXCEPT ![n].version    = m.version, ![n].tieBreaker = m.tieBreaker],
\*                         IF nodeState[n] \in {"valid", "invalid", "replay"}
\*                              THEN 
\*                              nodeState' = [nodeState EXCEPT ![n] = "invalid"]
\*                              ELSE 
\*                              nodeState' = [nodeState EXCEPT ![n] = "invalid_write"],
\*                         UNCHANGED <<nodeLastWriteTS, aliveNodes, nodeRcvedAcks, epochID, nodeWriteEpochID, msgsVAL, msgsINV>>,
\*                         NEW VARI \in H_NODES',
\*                         greaterTS(m.version, m.tieBreaker, nodeTS[n].version, nodeTS[n].tieBreaker)
\*                  PROVE  ((nodeLastWriteTS[VARI].tieBreaker = VARI) \/ ((nodeState[VARI] \in {"valid", "invalid", "replay"})))'
\*       BY DEF HRcvInvNewer, HRcvInvNewerAction, Inv627_R9_0_I2
\*     <2>1. CASE (m.version) > (nodeTS[n].version)
\*       BY <2>1 DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv627_R9_0_I2
\*     <2>2. CASE /\   (m.version) = (nodeTS[n].version)
\*                /\  (m.tieBreaker) > (nodeTS[n].tieBreaker)
\*       BY <2>2 DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv627_R9_0_I2
\*     <2>3. QED
\*       BY <2>1, <2>2 DEF greaterTS
\*   \* (Inv627_R9_0_I2,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv627_R9_0_I2 /\ HFollowerWriteReplayAction => Inv627_R9_0_I2' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv627_R9_0_I2
\*   \* (Inv627_R9_0_I2,HRcvValAction)
\*   <1>4. TypeOK /\ Inv627_R9_0_I2 /\ HRcvValAction => Inv627_R9_0_I2' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv627_R9_0_I2
\*   \* (Inv627_R9_0_I2,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv627_R9_0_I2 /\ HCoordWriteReplayAction => Inv627_R9_0_I2' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv627_R9_0_I2
\*   \* (Inv627_R9_0_I2,HWriteAction)
\*   <1>6. TypeOK /\ Inv627_R9_0_I2 /\ HWriteAction => Inv627_R9_0_I2' BY DEF TypeOK,HWriteAction,HWrite,Inv627_R9_0_I2
\*   \* (Inv627_R9_0_I2,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv627_R9_0_I2 /\ HRcvAckAction => Inv627_R9_0_I2' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv627_R9_0_I2
\*   \* (Inv627_R9_0_I2,HSendValsAction)
\*   <1>8. TypeOK /\ Inv627_R9_0_I2 /\ HSendValsAction => Inv627_R9_0_I2' BY DEF TypeOK,HSendValsAction,HSendVals,Inv627_R9_0_I2,receivedAllAcks,VALMessage
\*   \* (Inv627_R9_0_I2,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv627_R9_0_I2 /\ NodeFailureAction => Inv627_R9_0_I2' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv627_R9_0_I2
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv5_R0_1_I2
\* THEOREM L_5 == TypeOK /\ Inv5_R0_1_I2 /\ Next => Inv5_R0_1_I2'
\*   \* (Inv5_R0_1_I2,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv5_R0_1_I2 /\ HRcvInvAction => Inv5_R0_1_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv5_R0_1_I2
\*   \* (Inv5_R0_1_I2,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv5_R0_1_I2 /\ HRcvInvNewerAction => Inv5_R0_1_I2' BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv5_R0_1_I2
\*   \* (Inv5_R0_1_I2,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv5_R0_1_I2 /\ HFollowerWriteReplayAction => Inv5_R0_1_I2' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv5_R0_1_I2
\*   \* (Inv5_R0_1_I2,HRcvValAction)
\*   <1>4. TypeOK /\ Inv5_R0_1_I2 /\ HRcvValAction => Inv5_R0_1_I2' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv5_R0_1_I2
\*   \* (Inv5_R0_1_I2,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv5_R0_1_I2 /\ HCoordWriteReplayAction => Inv5_R0_1_I2' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv5_R0_1_I2
\*   \* (Inv5_R0_1_I2,HWriteAction)
\*   <1>6. TypeOK /\ Inv5_R0_1_I2 /\ HWriteAction => Inv5_R0_1_I2' BY DEF TypeOK,HWriteAction,HWrite,Inv5_R0_1_I2
\*   \* (Inv5_R0_1_I2,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv5_R0_1_I2 /\ HRcvAckAction => Inv5_R0_1_I2' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv5_R0_1_I2
\*   \* (Inv5_R0_1_I2,HSendValsAction)
\*   <1>8. TypeOK /\ Inv5_R0_1_I2 /\ HSendValsAction => Inv5_R0_1_I2' BY DEF TypeOK,HSendValsAction,HSendVals,Inv5_R0_1_I2,receivedAllAcks,VALMessage
\*   \* (Inv5_R0_1_I2,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv5_R0_1_I2 /\ NodeFailureAction => Inv5_R0_1_I2' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv5_R0_1_I2
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv3096_R0_0_I2
\* THEOREM L_6 == TypeOK /\ Inv29_R2_0_I1 /\ Inv14828_R0_0_I2 /\ Inv548_R0_1_I2 /\ Inv2701_R0_0_I2 /\ Inv4085_R0_0_I2 /\ Inv3029_R2_0_I1 /\ Inv2018_R0_0_I2 /\ Inv3096_R0_0_I2 /\ Next => Inv3096_R0_0_I2'
\*     <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
  
\*   \* (Inv3096_R0_0_I2,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv3096_R0_0_I2 /\ HRcvInvAction => Inv3096_R0_0_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv3096_R0_0_I2
\*   \* (Inv3096_R0_0_I2,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv29_R2_0_I1 /\ Inv14828_R0_0_I2 /\ Inv548_R0_1_I2 /\ Inv2701_R0_0_I2 /\ Inv4085_R0_0_I2 /\ Inv3029_R2_0_I1 /\ Inv2018_R0_0_I2 /\ Inv3096_R0_0_I2 /\ HRcvInvNewerAction => Inv3096_R0_0_I2' BY DEF TypeOK,Inv29_R2_0_I1,Inv14828_R0_0_I2,Inv548_R0_1_I2,Inv2701_R0_0_I2,Inv4085_R0_0_I2,Inv3029_R2_0_I1,Inv2018_R0_0_I2,HRcvInvNewerAction,HRcvInvNewer,Inv3096_R0_0_I2
\*   \* (Inv3096_R0_0_I2,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv3096_R0_0_I2 /\ HFollowerWriteReplayAction => Inv3096_R0_0_I2' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv3096_R0_0_I2
\*   \* (Inv3096_R0_0_I2,HRcvValAction)
\*   <1>4. TypeOK /\ Inv3096_R0_0_I2 /\ HRcvValAction => Inv3096_R0_0_I2' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv3096_R0_0_I2
\*   \* (Inv3096_R0_0_I2,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv3096_R0_0_I2 /\ HCoordWriteReplayAction => Inv3096_R0_0_I2' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv3096_R0_0_I2
\*   \* (Inv3096_R0_0_I2,HWriteAction)
\*   <1>6. TypeOK /\ Inv3096_R0_0_I2 /\ HWriteAction => Inv3096_R0_0_I2' BY DEF TypeOK,HWriteAction,HWrite,Inv3096_R0_0_I2
\*   \* (Inv3096_R0_0_I2,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv3096_R0_0_I2 /\ HRcvAckAction => Inv3096_R0_0_I2' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv3096_R0_0_I2
\*   \* (Inv3096_R0_0_I2,HSendValsAction)
\*   <1>8. TypeOK /\ Inv3096_R0_0_I2 /\ HSendValsAction => Inv3096_R0_0_I2' BY DEF TypeOK,HSendValsAction,HSendVals,Inv3096_R0_0_I2,receivedAllAcks,VALMessage
\*   \* (Inv3096_R0_0_I2,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv3096_R0_0_I2 /\ NodeFailureAction => Inv3096_R0_0_I2' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv3096_R0_0_I2
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next

\* LEMMA B1 == 
\*     /\ \A VARMINVI \in msgsINV :  (~(VARMINVI.epochID > epochID) <=> (VARMINVI.epochID <= epochID))
\*     /\ \A VARMINVI \in msgsINV, n \in Nat:  (~(VARMINVI.epochID > n) => ~(VARMINVI.epochID > n + 1))
\* USE B1

\* \*** Inv29_R2_0_I1
\* THEOREM L_7 == TypeOK /\ Inv29_R2_0_I1 /\ Next => Inv29_R2_0_I1'
\*     <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
  
\*   \* (Inv29_R2_0_I1,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv29_R2_0_I1 /\ HRcvInvAction => Inv29_R2_0_I1' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv29_R2_0_I1
\*   \* (Inv29_R2_0_I1,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv29_R2_0_I1 /\ HRcvInvNewerAction => Inv29_R2_0_I1' BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv29_R2_0_I1
\*   \* (Inv29_R2_0_I1,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv29_R2_0_I1 /\ HFollowerWriteReplayAction => Inv29_R2_0_I1' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv29_R2_0_I1
\*   \* (Inv29_R2_0_I1,HRcvValAction)
\*   <1>4. TypeOK /\ Inv29_R2_0_I1 /\ HRcvValAction => Inv29_R2_0_I1' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv29_R2_0_I1
\*   \* (Inv29_R2_0_I1,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv29_R2_0_I1 /\ HCoordWriteReplayAction => Inv29_R2_0_I1' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv29_R2_0_I1
\*   \* (Inv29_R2_0_I1,HWriteAction)
\*   <1>6. TypeOK /\ Inv29_R2_0_I1 /\ HWriteAction => Inv29_R2_0_I1' BY DEF TypeOK,HWriteAction,HWrite,Inv29_R2_0_I1
\*   \* (Inv29_R2_0_I1,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv29_R2_0_I1 /\ HRcvAckAction => Inv29_R2_0_I1' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv29_R2_0_I1
\*   \* (Inv29_R2_0_I1,HSendValsAction)
\*   <1>8. TypeOK /\ Inv29_R2_0_I1 /\ HSendValsAction => Inv29_R2_0_I1' BY DEF TypeOK,HSendValsAction,HSendVals,Inv29_R2_0_I1,receivedAllAcks,VALMessage
\*   \* (Inv29_R2_0_I1,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv29_R2_0_I1 /\ NodeFailureAction => Inv29_R2_0_I1' 
\*     <2> SUFFICES ASSUME TypeOK /\ Inv29_R2_0_I1 /\ NodeFailureAction,
\*                         NEW VARMINVI \in msgsINV'
\*                  PROVE  (~(VARMINVI.epochID > epochID))'
\*       BY DEF Inv29_R2_0_I1
\*     <2>1. (VARMINVI \in msgsINV)
\*           BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv29_R2_0_I1, INVMessage
\*      <2>2. (VARMINVI.epochID <= epochID)
\*           BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv29_R2_0_I1, INVMessage
\*      <2>3. ~ (VARMINVI.epochID > (epochID + 1))
\*            BY <2>2 DEF TypeOK,NodeFailureAction,NodeFailure,Inv29_R2_0_I1, INVMessage
     
\*     <2> QED
\*       BY <2>1, <2>2, <2>3 DEF TypeOK,NodeFailureAction,NodeFailure,Inv29_R2_0_I1, INVMessage
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv14828_R0_0_I2
\* THEOREM L_8 == TypeOK /\ Inv3029_R2_0_I1 /\ Inv3096_R0_0_I2 /\ Inv14828_R0_0_I2 /\ Next => Inv14828_R0_0_I2'
\*     <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
  
\*   \* (Inv14828_R0_0_I2,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv14828_R0_0_I2 /\ HRcvInvAction => Inv14828_R0_0_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv14828_R0_0_I2
\*   \* (Inv14828_R0_0_I2,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv3029_R2_0_I1 /\ Inv3096_R0_0_I2 /\ Inv14828_R0_0_I2 /\ HRcvInvNewerAction => Inv14828_R0_0_I2' BY DEF TypeOK,Inv3029_R2_0_I1,Inv3096_R0_0_I2,HRcvInvNewerAction,HRcvInvNewer,Inv14828_R0_0_I2
\*   \* (Inv14828_R0_0_I2,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv14828_R0_0_I2 /\ HFollowerWriteReplayAction => Inv14828_R0_0_I2' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv14828_R0_0_I2
\*   \* (Inv14828_R0_0_I2,HRcvValAction)
\*   <1>4. TypeOK /\ Inv14828_R0_0_I2 /\ HRcvValAction => Inv14828_R0_0_I2' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv14828_R0_0_I2
\*   \* (Inv14828_R0_0_I2,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv14828_R0_0_I2 /\ HCoordWriteReplayAction => Inv14828_R0_0_I2' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv14828_R0_0_I2
\*   \* (Inv14828_R0_0_I2,HWriteAction)
\*   <1>6. TypeOK /\ Inv14828_R0_0_I2 /\ HWriteAction => Inv14828_R0_0_I2' BY DEF TypeOK,HWriteAction,HWrite,Inv14828_R0_0_I2
\*   \* (Inv14828_R0_0_I2,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv14828_R0_0_I2 /\ HRcvAckAction => Inv14828_R0_0_I2' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv14828_R0_0_I2
\*   \* (Inv14828_R0_0_I2,HSendValsAction)
\*   <1>8. TypeOK /\ Inv14828_R0_0_I2 /\ HSendValsAction => Inv14828_R0_0_I2' BY DEF TypeOK,HSendValsAction,HSendVals,Inv14828_R0_0_I2,receivedAllAcks,VALMessage
\*   \* (Inv14828_R0_0_I2,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv14828_R0_0_I2 /\ NodeFailureAction => Inv14828_R0_0_I2' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv14828_R0_0_I2
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv3029_R2_0_I1
\* THEOREM L_9 == TypeOK /\ Inv3096_R0_0_I2 /\ Inv14828_R0_0_I2 /\ Inv3096_R0_0_I2 /\ Inv14828_R0_0_I2 /\ Inv3029_R2_0_I1 /\ Next => Inv3029_R2_0_I1'
\*     <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
  
\*   \* (Inv3029_R2_0_I1,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv3029_R2_0_I1 /\ HRcvInvAction => Inv3029_R2_0_I1' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv3029_R2_0_I1
\*   \* (Inv3029_R2_0_I1,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv3029_R2_0_I1 /\ HRcvInvNewerAction => Inv3029_R2_0_I1' BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv3029_R2_0_I1
\*   \* (Inv3029_R2_0_I1,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv3096_R0_0_I2 /\ Inv14828_R0_0_I2 /\ Inv3029_R2_0_I1 /\ HFollowerWriteReplayAction => Inv3029_R2_0_I1' BY DEF TypeOK,Inv3096_R0_0_I2,Inv14828_R0_0_I2,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv3029_R2_0_I1
\*   \* (Inv3029_R2_0_I1,HRcvValAction)
\*   <1>4. TypeOK /\ Inv3029_R2_0_I1 /\ HRcvValAction => Inv3029_R2_0_I1' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv3029_R2_0_I1
\*   \* (Inv3029_R2_0_I1,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv3096_R0_0_I2 /\ Inv14828_R0_0_I2 /\ Inv3029_R2_0_I1 /\ HCoordWriteReplayAction => Inv3029_R2_0_I1' BY DEF TypeOK,Inv3096_R0_0_I2,Inv14828_R0_0_I2,HCoordWriteReplayAction,HCoordWriteReplay,Inv3029_R2_0_I1
\*   \* (Inv3029_R2_0_I1,HWriteAction)
\*   <1>6. TypeOK /\ Inv3029_R2_0_I1 /\ HWriteAction => Inv3029_R2_0_I1' BY DEF TypeOK,HWriteAction,HWrite,Inv3029_R2_0_I1
\*   \* (Inv3029_R2_0_I1,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv3029_R2_0_I1 /\ HRcvAckAction => Inv3029_R2_0_I1' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv3029_R2_0_I1
\*   \* (Inv3029_R2_0_I1,HSendValsAction)
\*   <1>8. TypeOK /\ Inv3029_R2_0_I1 /\ HSendValsAction => Inv3029_R2_0_I1' BY DEF TypeOK,HSendValsAction,HSendVals,Inv3029_R2_0_I1,receivedAllAcks,VALMessage
\*   \* (Inv3029_R2_0_I1,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv3029_R2_0_I1 /\ NodeFailureAction => Inv3029_R2_0_I1' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv3029_R2_0_I1
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv548_R0_1_I2
\* THEOREM L_10 == TypeOK /\ Inv3029_R2_0_I1 /\ Inv548_R0_1_I2 /\ Next => Inv548_R0_1_I2'
\*   <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
\*   \* (Inv548_R0_1_I2,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv548_R0_1_I2 /\ HRcvInvAction => Inv548_R0_1_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv548_R0_1_I2
\*   \* (Inv548_R0_1_I2,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv3029_R2_0_I1 /\ Inv548_R0_1_I2 /\ HRcvInvNewerAction => Inv548_R0_1_I2' BY DEF TypeOK,Inv3029_R2_0_I1,HRcvInvNewerAction,HRcvInvNewer,Inv548_R0_1_I2
\*   \* (Inv548_R0_1_I2,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv548_R0_1_I2 /\ HFollowerWriteReplayAction => Inv548_R0_1_I2' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv548_R0_1_I2
\*   \* (Inv548_R0_1_I2,HRcvValAction)
\*   <1>4. TypeOK /\ Inv548_R0_1_I2 /\ HRcvValAction => Inv548_R0_1_I2' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv548_R0_1_I2
\*   \* (Inv548_R0_1_I2,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv548_R0_1_I2 /\ HCoordWriteReplayAction => Inv548_R0_1_I2' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv548_R0_1_I2
\*   \* (Inv548_R0_1_I2,HWriteAction)
\*   <1>6. TypeOK /\ Inv548_R0_1_I2 /\ HWriteAction => Inv548_R0_1_I2' BY DEF TypeOK,HWriteAction,HWrite,Inv548_R0_1_I2
\*   \* (Inv548_R0_1_I2,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv548_R0_1_I2 /\ HRcvAckAction => Inv548_R0_1_I2' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv548_R0_1_I2
\*   \* (Inv548_R0_1_I2,HSendValsAction)
\*   <1>8. TypeOK /\ Inv548_R0_1_I2 /\ HSendValsAction => Inv548_R0_1_I2' BY DEF TypeOK,HSendValsAction,HSendVals,Inv548_R0_1_I2,receivedAllAcks,VALMessage
\*   \* (Inv548_R0_1_I2,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv548_R0_1_I2 /\ NodeFailureAction => Inv548_R0_1_I2' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv548_R0_1_I2
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv2701_R0_0_I2
\* THEOREM L_11 == TypeOK /\ Inv3029_R2_0_I1 /\ Inv2701_R0_0_I2 /\ Next => Inv2701_R0_0_I2'
\*   <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
\*   \* (Inv2701_R0_0_I2,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv2701_R0_0_I2 /\ HRcvInvAction => Inv2701_R0_0_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv2701_R0_0_I2
\*   \* (Inv2701_R0_0_I2,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv3029_R2_0_I1 /\ Inv2701_R0_0_I2 /\ HRcvInvNewerAction => Inv2701_R0_0_I2' BY DEF TypeOK,Inv3029_R2_0_I1,HRcvInvNewerAction,HRcvInvNewer,Inv2701_R0_0_I2
\*   \* (Inv2701_R0_0_I2,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv2701_R0_0_I2 /\ HFollowerWriteReplayAction => Inv2701_R0_0_I2' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv2701_R0_0_I2
\*   \* (Inv2701_R0_0_I2,HRcvValAction)
\*   <1>4. TypeOK /\ Inv2701_R0_0_I2 /\ HRcvValAction => Inv2701_R0_0_I2' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv2701_R0_0_I2
\*   \* (Inv2701_R0_0_I2,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv2701_R0_0_I2 /\ HCoordWriteReplayAction => Inv2701_R0_0_I2' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv2701_R0_0_I2
\*   \* (Inv2701_R0_0_I2,HWriteAction)
\*   <1>6. TypeOK /\ Inv2701_R0_0_I2 /\ HWriteAction => Inv2701_R0_0_I2' BY DEF TypeOK,HWriteAction,HWrite,Inv2701_R0_0_I2
\*   \* (Inv2701_R0_0_I2,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv2701_R0_0_I2 /\ HRcvAckAction => Inv2701_R0_0_I2' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv2701_R0_0_I2
\*   \* (Inv2701_R0_0_I2,HSendValsAction)
\*   <1>8. TypeOK /\ Inv2701_R0_0_I2 /\ HSendValsAction => Inv2701_R0_0_I2' BY DEF TypeOK,HSendValsAction,HSendVals,Inv2701_R0_0_I2,receivedAllAcks,VALMessage
\*   \* (Inv2701_R0_0_I2,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv2701_R0_0_I2 /\ NodeFailureAction => Inv2701_R0_0_I2' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv2701_R0_0_I2
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv4085_R0_0_I2
\* THEOREM L_12 == TypeOK /\ Inv2345_R0_0_I2 /\ Inv3025_R1_0_I2 /\ Inv4085_R0_0_I2 /\ Next => Inv4085_R0_0_I2'
\*   \* (Inv4085_R0_0_I2,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv4085_R0_0_I2 /\ HRcvInvAction => Inv4085_R0_0_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv4085_R0_0_I2
\*   \* (Inv4085_R0_0_I2,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv4085_R0_0_I2 /\ HRcvInvNewerAction => Inv4085_R0_0_I2' 
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv4085_R0_0_I2,
\*                         TRUE,
\*                         NEW n \in aliveNodes, NEW m \in msgsINV,
\*                         n \in aliveNodes,
\*                         m \in msgsINV,
\*                         m.type     = "INV",
\*                         m.epochID  = epochID,
\*                         m.sender  # n,
\*                         msgsACK' = msgsACK \cup {[type       |-> "ACK",
\*                                                   sender     |-> n,   
\*                                                   epochID    |-> epochID,
\*                                                   version    |-> m.version,
\*                                                   tieBreaker |-> m.tieBreaker]},
\*                         nodeLastWriter' = [nodeLastWriter EXCEPT ![n] = m.sender],
\*                         nodeTS' = [nodeTS EXCEPT ![n].version    = m.version, ![n].tieBreaker = m.tieBreaker],
\*                         IF nodeState[n] \in {"valid", "invalid", "replay"}
\*                              THEN 
\*                              nodeState' = [nodeState EXCEPT ![n] = "invalid"]
\*                              ELSE 
\*                              nodeState' = [nodeState EXCEPT ![n] = "invalid_write"],
\*                         UNCHANGED <<nodeLastWriteTS, aliveNodes, nodeRcvedAcks, epochID, nodeWriteEpochID, msgsVAL, msgsINV>>,
\*                         NEW VARI \in H_NODES',
\*                         NEW VARJ \in H_NODES',
\*                         greaterTS(m.version, m.tieBreaker, nodeTS[n].version, nodeTS[n].tieBreaker)
\*                  PROVE  ((greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(VARI \in aliveNodes) \/ (~(nodeState[VARJ] = "valid"))))'
\*       BY DEF HRcvInvNewer, HRcvInvNewerAction, Inv4085_R0_0_I2
\*     <2> USE DEF greaterOrEqualTS, greaterTS, equalTS
\*     <2>1. CASE (m.version) > (nodeTS[n].version)
\*       BY <2>1 DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv4085_R0_0_I2
\*     <2>2. CASE /\   (m.version) = (nodeTS[n].version)
\*                /\  (m.tieBreaker) > (nodeTS[n].tieBreaker)
\*       BY <2>2 DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv4085_R0_0_I2
\*     <2>3. QED
\*       BY <2>1, <2>2 DEF greaterTS
    
\*   \* (Inv4085_R0_0_I2,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv4085_R0_0_I2 /\ HFollowerWriteReplayAction => Inv4085_R0_0_I2' 
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv4085_R0_0_I2,
\*                         TRUE,
\*                         NEW n \in aliveNodes,
\*                         HFollowerWriteReplay(n),
\*                         NEW VARI \in H_NODES',
\*                         NEW VARJ \in H_NODES'
\*                  PROVE  ((greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(VARI \in aliveNodes) \/ (~(nodeState[VARJ] = "valid"))))'
\*       BY DEF HFollowerWriteReplayAction, Inv4085_R0_0_I2
\*     <2> QED
\*       BY FS_Subset, FS_Singleton DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv4085_R0_0_I2, isAlive
\*   \* (Inv4085_R0_0_I2,HRcvValAction)
\*   <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
\*   <1>4. TypeOK /\ Inv2345_R0_0_I2 /\ Inv4085_R0_0_I2 /\ HRcvValAction => Inv4085_R0_0_I2' 
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv2345_R0_0_I2,
\*                         Inv4085_R0_0_I2,
\*                         TRUE,
\*                         NEW n \in aliveNodes, NEW m \in msgsVAL,
\*                         HRcvVal(n, m),
\*                         NEW VARI \in H_NODES',
\*                         NEW VARJ \in H_NODES'
\*                  PROVE  ((greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(VARI \in aliveNodes) \/ (~(nodeState[VARJ] = "valid"))))'
\*       BY DEF HRcvValAction, Inv4085_R0_0_I2
\*     <2> QED
\*       BY FS_Subset, FS_Singleton, FS_Difference DEF TypeOK,Inv2345_R0_0_I2,HRcvValAction,HRcvVal,Inv4085_R0_0_I2
\*   \* (Inv4085_R0_0_I2,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv4085_R0_0_I2 /\ HCoordWriteReplayAction => Inv4085_R0_0_I2' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv4085_R0_0_I2
\*   \* (Inv4085_R0_0_I2,HWriteAction)
\*   <1>6. TypeOK /\ Inv4085_R0_0_I2 /\ HWriteAction => Inv4085_R0_0_I2' 
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv4085_R0_0_I2,
\*                         TRUE,
\*                         NEW n \in aliveNodes,
\*                         HWrite(n),
\*                         NEW VARI \in H_NODES'
\*                  PROVE  (\A VARJ \in H_NODES : (greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(VARI \in aliveNodes) \/ (~(nodeState[VARJ] = "valid"))))'
\*       BY DEF HWriteAction, Inv4085_R0_0_I2
\*     <2> QED
\*       BY FS_Subset, FS_Singleton DEF TypeOK,HWriteAction,HWrite,Inv4085_R0_0_I2
\*   \* (Inv4085_R0_0_I2,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv4085_R0_0_I2 /\ HRcvAckAction => Inv4085_R0_0_I2' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv4085_R0_0_I2
\*   \* (Inv4085_R0_0_I2,HSendValsAction)
\*   <1>8. TypeOK /\ Inv3025_R1_0_I2 /\ Inv4085_R0_0_I2 /\ HSendValsAction => Inv4085_R0_0_I2' BY DEF TypeOK,Inv3025_R1_0_I2,HSendValsAction,HSendVals,Inv4085_R0_0_I2,receivedAllAcks,VALMessage
\*   \* (Inv4085_R0_0_I2,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv4085_R0_0_I2 /\ NodeFailureAction => Inv4085_R0_0_I2' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv4085_R0_0_I2
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv3025_R1_0_I2
\* THEOREM L_13 == TypeOK /\ Inv627_R9_0_I2 /\ Inv3096_R0_0_I2 /\ Inv1666_R10_0_I1 /\ Inv28_R17_0_I1 /\ Inv2018_R0_0_I2 /\ Inv3025_R1_0_I2 /\ Next => Inv3025_R1_0_I2'
\*   <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
\*   \* (Inv3025_R1_0_I2,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv3025_R1_0_I2 /\ HRcvInvAction => Inv3025_R1_0_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv3025_R1_0_I2
\*   \* (Inv3025_R1_0_I2,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv3025_R1_0_I2 /\ HRcvInvNewerAction => Inv3025_R1_0_I2' BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv3025_R1_0_I2
\*   \* (Inv3025_R1_0_I2,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv3025_R1_0_I2 /\ HFollowerWriteReplayAction => Inv3025_R1_0_I2' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv3025_R1_0_I2
\*   \* (Inv3025_R1_0_I2,HRcvValAction)
\*   <1>4. TypeOK /\ Inv3025_R1_0_I2 /\ HRcvValAction => Inv3025_R1_0_I2' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv3025_R1_0_I2
\*   \* (Inv3025_R1_0_I2,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv3025_R1_0_I2 /\ HCoordWriteReplayAction => Inv3025_R1_0_I2' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv3025_R1_0_I2
\*   \* (Inv3025_R1_0_I2,HWriteAction)
\*   <1>6. TypeOK /\ Inv3025_R1_0_I2 /\ HWriteAction => Inv3025_R1_0_I2' BY DEF TypeOK,HWriteAction,HWrite,Inv3025_R1_0_I2
\*   \* (Inv3025_R1_0_I2,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv627_R9_0_I2 /\ Inv3096_R0_0_I2 /\ Inv1666_R10_0_I1 /\ Inv28_R17_0_I1 /\ Inv2018_R0_0_I2 /\ Inv3025_R1_0_I2 /\ HRcvAckAction => Inv3025_R1_0_I2' BY DEF TypeOK,Inv627_R9_0_I2,Inv3096_R0_0_I2,Inv1666_R10_0_I1,Inv28_R17_0_I1,Inv2018_R0_0_I2,HRcvAckAction,HRcvAck,Inv3025_R1_0_I2
\*   \* (Inv3025_R1_0_I2,HSendValsAction)
\*   <1>8. TypeOK /\ Inv3025_R1_0_I2 /\ HSendValsAction => Inv3025_R1_0_I2' BY DEF TypeOK,HSendValsAction,HSendVals,Inv3025_R1_0_I2,receivedAllAcks,VALMessage
\*   \* (Inv3025_R1_0_I2,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv3025_R1_0_I2 /\ NodeFailureAction => Inv3025_R1_0_I2' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv3025_R1_0_I2
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv1666_R10_0_I1
\* THEOREM L_14 == TypeOK /\ Inv3029_R2_0_I1 /\ Inv1666_R10_0_I1 /\ Next => Inv1666_R10_0_I1'
\*     <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
\*   \* (Inv1666_R10_0_I1,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv1666_R10_0_I1 /\ HRcvInvAction => Inv1666_R10_0_I1' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv1666_R10_0_I1
\*   \* (Inv1666_R10_0_I1,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv3029_R2_0_I1 /\ Inv1666_R10_0_I1 /\ HRcvInvNewerAction => Inv1666_R10_0_I1' BY DEF TypeOK,Inv3029_R2_0_I1,HRcvInvNewerAction,HRcvInvNewer,Inv1666_R10_0_I1
\*   \* (Inv1666_R10_0_I1,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv1666_R10_0_I1 /\ HFollowerWriteReplayAction => Inv1666_R10_0_I1' 
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv1666_R10_0_I1,
\*                         TRUE,
\*                         NEW n \in aliveNodes,
\*                         HFollowerWriteReplay(n),
\*                         NEW VARI \in H_NODES'
\*                  PROVE  ((nodeTS[VARI] = nodeLastWriteTS[VARI]) \/ (~(nodeTS[VARI].tieBreaker = VARI)))'
\*       BY DEF HFollowerWriteReplayAction, Inv1666_R10_0_I1
\*     <2> QED
\*       BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv1666_R10_0_I1
\*   \* (Inv1666_R10_0_I1,HRcvValAction)
\*   <1>4. TypeOK /\ Inv1666_R10_0_I1 /\ HRcvValAction => Inv1666_R10_0_I1' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv1666_R10_0_I1
\*   \* (Inv1666_R10_0_I1,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv1666_R10_0_I1 /\ HCoordWriteReplayAction => Inv1666_R10_0_I1' 
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv1666_R10_0_I1,
\*                         TRUE,
\*                         NEW n \in aliveNodes,
\*                         HCoordWriteReplay(n),
\*                         NEW VARI \in H_NODES'
\*                  PROVE  ((nodeTS[VARI] = nodeLastWriteTS[VARI]) \/ (~(nodeTS[VARI].tieBreaker = VARI)))'
\*       BY DEF HCoordWriteReplayAction, Inv1666_R10_0_I1
\*     <2> QED
\*       BY FS_Subset, FS_Singleton DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv1666_R10_0_I1
\*   \* (Inv1666_R10_0_I1,HWriteAction)
\*   <1>6. TypeOK /\ Inv1666_R10_0_I1 /\ HWriteAction => Inv1666_R10_0_I1' 
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv1666_R10_0_I1,
\*                         TRUE,
\*                         NEW n \in aliveNodes,
\*                         HWrite(n),
\*                         NEW VARI \in H_NODES'
\*                  PROVE  ((nodeTS[VARI] = nodeLastWriteTS[VARI]) \/ (~(nodeTS[VARI].tieBreaker = VARI)))'
\*       BY DEF HWriteAction, Inv1666_R10_0_I1
\*     <2> QED
\*       BY FS_Subset, FS_Singleton DEF TypeOK,HWriteAction,HWrite,Inv1666_R10_0_I1
\*   \* (Inv1666_R10_0_I1,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv1666_R10_0_I1 /\ HRcvAckAction => Inv1666_R10_0_I1' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv1666_R10_0_I1
\*   \* (Inv1666_R10_0_I1,HSendValsAction)
\*   <1>8. TypeOK /\ Inv1666_R10_0_I1 /\ HSendValsAction => Inv1666_R10_0_I1' BY DEF TypeOK,HSendValsAction,HSendVals,Inv1666_R10_0_I1,receivedAllAcks,VALMessage
\*   \* (Inv1666_R10_0_I1,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv1666_R10_0_I1 /\ NodeFailureAction => Inv1666_R10_0_I1' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv1666_R10_0_I1
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv28_R17_0_I1
\* THEOREM L_15 == TypeOK /\ Inv28_R17_0_I1 /\ Next => Inv28_R17_0_I1'
\*  <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
\*   \* (Inv28_R17_0_I1,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv28_R17_0_I1 /\ HRcvInvAction => Inv28_R17_0_I1' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv28_R17_0_I1
\*   \* (Inv28_R17_0_I1,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv28_R17_0_I1 /\ HRcvInvNewerAction => Inv28_R17_0_I1' BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv28_R17_0_I1
\*   \* (Inv28_R17_0_I1,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv28_R17_0_I1 /\ HFollowerWriteReplayAction => Inv28_R17_0_I1' 
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv28_R17_0_I1,
\*                         TRUE,
\*                         NEW n \in aliveNodes,
\*                         HFollowerWriteReplay(n),
\*                         NEW VARI \in H_NODES'
\*                  PROVE  ((nodeTS[VARI] = nodeLastWriteTS[VARI]) \/ (~(nodeState[VARI] = "replay")))'
\*       BY DEF HFollowerWriteReplayAction, Inv28_R17_0_I1
\*     <2> QED
\*       BY FS_Subset, FS_Singleton DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv28_R17_0_I1
\*   \* (Inv28_R17_0_I1,HRcvValAction)
\*   <1>4. TypeOK /\ Inv28_R17_0_I1 /\ HRcvValAction => Inv28_R17_0_I1' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv28_R17_0_I1
\*   \* (Inv28_R17_0_I1,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv28_R17_0_I1 /\ HCoordWriteReplayAction => Inv28_R17_0_I1' 
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv28_R17_0_I1,
\*                         TRUE,
\*                         NEW n \in aliveNodes,
\*                         HCoordWriteReplay(n),
\*                         NEW VARI \in H_NODES'
\*                  PROVE  ((nodeTS[VARI] = nodeLastWriteTS[VARI]) \/ (~(nodeState[VARI] = "replay")))'
\*       BY DEF HCoordWriteReplayAction, Inv28_R17_0_I1
\*     <2> QED
\*       BY FS_Subset, FS_Singleton, FS_Difference DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv28_R17_0_I1, receivedAllAcks
\*   \* (Inv28_R17_0_I1,HWriteAction)
\*   <1>6. TypeOK /\ Inv28_R17_0_I1 /\ HWriteAction => Inv28_R17_0_I1' BY DEF TypeOK,HWriteAction,HWrite,Inv28_R17_0_I1
\*   \* (Inv28_R17_0_I1,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv28_R17_0_I1 /\ HRcvAckAction => Inv28_R17_0_I1' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv28_R17_0_I1
\*   \* (Inv28_R17_0_I1,HSendValsAction)
\*   <1>8. TypeOK /\ Inv28_R17_0_I1 /\ HSendValsAction => Inv28_R17_0_I1' BY DEF TypeOK,HSendValsAction,HSendVals,Inv28_R17_0_I1,receivedAllAcks,VALMessage
\*   \* (Inv28_R17_0_I1,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv28_R17_0_I1 /\ NodeFailureAction => Inv28_R17_0_I1' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv28_R17_0_I1
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv2018_R0_0_I2
\* THEOREM L_16 == TypeOK /\ Inv2018_R0_0_I2 /\ Next => Inv2018_R0_0_I2'
\*  <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
\*   \* (Inv2018_R0_0_I2,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv2018_R0_0_I2 /\ HRcvInvAction => Inv2018_R0_0_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv2018_R0_0_I2
\*   \* (Inv2018_R0_0_I2,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv2018_R0_0_I2 /\ HRcvInvNewerAction => Inv2018_R0_0_I2' BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv2018_R0_0_I2
\*   \* (Inv2018_R0_0_I2,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv2018_R0_0_I2 /\ HFollowerWriteReplayAction => Inv2018_R0_0_I2' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv2018_R0_0_I2
\*   \* (Inv2018_R0_0_I2,HRcvValAction)
\*   <1>4. TypeOK /\ Inv2018_R0_0_I2 /\ HRcvValAction => Inv2018_R0_0_I2' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv2018_R0_0_I2
\*   \* (Inv2018_R0_0_I2,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv2018_R0_0_I2 /\ HCoordWriteReplayAction => Inv2018_R0_0_I2' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv2018_R0_0_I2
\*   \* (Inv2018_R0_0_I2,HWriteAction)
\*   <1>6. TypeOK /\ Inv2018_R0_0_I2 /\ HWriteAction => Inv2018_R0_0_I2' BY DEF TypeOK,HWriteAction,HWrite,Inv2018_R0_0_I2
\*   \* (Inv2018_R0_0_I2,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv2018_R0_0_I2 /\ HRcvAckAction => Inv2018_R0_0_I2' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv2018_R0_0_I2
\*   \* (Inv2018_R0_0_I2,HSendValsAction)
\*   <1>8. TypeOK /\ Inv2018_R0_0_I2 /\ HSendValsAction => Inv2018_R0_0_I2' BY DEF TypeOK,HSendValsAction,HSendVals,Inv2018_R0_0_I2,receivedAllAcks,VALMessage
\*   \* (Inv2018_R0_0_I2,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv2018_R0_0_I2 /\ NodeFailureAction => Inv2018_R0_0_I2' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv2018_R0_0_I2
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv4_R0_1_I2
\* THEOREM L_17 == TypeOK /\ Inv5_R0_1_I2 /\ Inv627_R9_0_I2 /\ Inv927_R9_0_I2 /\ Inv4_R0_1_I2 /\ Next => Inv4_R0_1_I2'
\*  <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
\*   \* (Inv4_R0_1_I2,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv4_R0_1_I2 /\ HRcvInvAction => Inv4_R0_1_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv4_R0_1_I2
\*   \* (Inv4_R0_1_I2,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv4_R0_1_I2 /\ HRcvInvNewerAction => Inv4_R0_1_I2' BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv4_R0_1_I2
\*   \* (Inv4_R0_1_I2,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv4_R0_1_I2 /\ HFollowerWriteReplayAction => Inv4_R0_1_I2' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv4_R0_1_I2
\*   \* (Inv4_R0_1_I2,HRcvValAction)
\*   <1>4. TypeOK /\ Inv4_R0_1_I2 /\ HRcvValAction => Inv4_R0_1_I2' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv4_R0_1_I2
\*   \* (Inv4_R0_1_I2,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv4_R0_1_I2 /\ HCoordWriteReplayAction => Inv4_R0_1_I2' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv4_R0_1_I2
\*   \* (Inv4_R0_1_I2,HWriteAction)
\*   <1>6. TypeOK /\ Inv4_R0_1_I2 /\ HWriteAction => Inv4_R0_1_I2' BY DEF TypeOK,HWriteAction,HWrite,Inv4_R0_1_I2
\*   \* (Inv4_R0_1_I2,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv5_R0_1_I2 /\ Inv627_R9_0_I2 /\ Inv927_R9_0_I2 /\ Inv4_R0_1_I2 /\ HRcvAckAction => Inv4_R0_1_I2' BY DEF TypeOK,Inv5_R0_1_I2,Inv627_R9_0_I2,Inv927_R9_0_I2,HRcvAckAction,HRcvAck,Inv4_R0_1_I2
\*   \* (Inv4_R0_1_I2,HSendValsAction)
\*   <1>8. TypeOK /\ Inv4_R0_1_I2 /\ HSendValsAction => Inv4_R0_1_I2' BY DEF TypeOK,HSendValsAction,HSendVals,Inv4_R0_1_I2,receivedAllAcks,VALMessage
\*   \* (Inv4_R0_1_I2,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv4_R0_1_I2 /\ NodeFailureAction => Inv4_R0_1_I2' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv4_R0_1_I2
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv927_R9_0_I2
\* THEOREM L_18 == TypeOK /\ Inv1_R21_0_I0 /\ Inv927_R9_0_I2 /\ Next => Inv927_R9_0_I2'
\*  <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
\*   \* (Inv927_R9_0_I2,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv927_R9_0_I2 /\ HRcvInvAction => Inv927_R9_0_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv927_R9_0_I2
\*   \* (Inv927_R9_0_I2,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv927_R9_0_I2 /\ HRcvInvNewerAction => Inv927_R9_0_I2' BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv927_R9_0_I2
\*   \* (Inv927_R9_0_I2,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv927_R9_0_I2 /\ HFollowerWriteReplayAction => Inv927_R9_0_I2' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv927_R9_0_I2
\*   \* (Inv927_R9_0_I2,HRcvValAction)
\*   <1>4. TypeOK /\ Inv927_R9_0_I2 /\ HRcvValAction => Inv927_R9_0_I2' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv927_R9_0_I2
\*   \* (Inv927_R9_0_I2,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv927_R9_0_I2 /\ HCoordWriteReplayAction => Inv927_R9_0_I2' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv927_R9_0_I2
\*   \* (Inv927_R9_0_I2,HWriteAction)
\*   <1>6. TypeOK /\ Inv927_R9_0_I2 /\ HWriteAction => Inv927_R9_0_I2' BY DEF TypeOK,HWriteAction,HWrite,Inv927_R9_0_I2
\*   \* (Inv927_R9_0_I2,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv927_R9_0_I2 /\ HRcvAckAction => Inv927_R9_0_I2' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv927_R9_0_I2
\*   \* (Inv927_R9_0_I2,HSendValsAction)
\*   <1>8. TypeOK /\ Inv927_R9_0_I2 /\ HSendValsAction => Inv927_R9_0_I2' BY DEF TypeOK,HSendValsAction,HSendVals,Inv927_R9_0_I2,receivedAllAcks,VALMessage
\*   \* (Inv927_R9_0_I2,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv1_R21_0_I0 /\ Inv927_R9_0_I2 /\ NodeFailureAction => Inv927_R9_0_I2' BY DEF TypeOK,Inv1_R21_0_I0,NodeFailureAction,NodeFailure,Inv927_R9_0_I2
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv1_R21_0_I0
\* THEOREM L_19 == TypeOK /\ Inv1_R21_0_I0 /\ Next => Inv1_R21_0_I0'
\*  <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
\*   \* (Inv1_R21_0_I0,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv1_R21_0_I0 /\ HRcvInvAction => Inv1_R21_0_I0' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv1_R21_0_I0
\*   \* (Inv1_R21_0_I0,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv1_R21_0_I0 /\ HRcvInvNewerAction => Inv1_R21_0_I0' BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv1_R21_0_I0
\*   \* (Inv1_R21_0_I0,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv1_R21_0_I0 /\ HFollowerWriteReplayAction => Inv1_R21_0_I0' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv1_R21_0_I0
\*   \* (Inv1_R21_0_I0,HRcvValAction)
\*   <1>4. TypeOK /\ Inv1_R21_0_I0 /\ HRcvValAction => Inv1_R21_0_I0' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv1_R21_0_I0
\*   \* (Inv1_R21_0_I0,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv1_R21_0_I0 /\ HCoordWriteReplayAction => Inv1_R21_0_I0' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv1_R21_0_I0
\*   \* (Inv1_R21_0_I0,HWriteAction)
\*   <1>6. TypeOK /\ Inv1_R21_0_I0 /\ HWriteAction => Inv1_R21_0_I0' BY DEF TypeOK,HWriteAction,HWrite,Inv1_R21_0_I0
\*   \* (Inv1_R21_0_I0,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv1_R21_0_I0 /\ HRcvAckAction => Inv1_R21_0_I0' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv1_R21_0_I0
\*   \* (Inv1_R21_0_I0,HSendValsAction)
\*   <1>8. TypeOK /\ Inv1_R21_0_I0 /\ HSendValsAction => Inv1_R21_0_I0' BY DEF TypeOK,HSendValsAction,HSendVals,Inv1_R21_0_I0,receivedAllAcks,VALMessage
\*   \* (Inv1_R21_0_I0,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv1_R21_0_I0 /\ NodeFailureAction => Inv1_R21_0_I0' 
\*     <2> SUFFICES ASSUME TypeOK /\ Inv1_R21_0_I0 /\ NodeFailureAction,
\*                         NEW VARMACKI \in msgsACK'
\*                  PROVE  (~(VARMACKI.epochID > epochID))'
\*       BY DEF Inv1_R21_0_I0
\*     <2> QED
\*       BY FS_Singleton DEF TypeOK,NodeFailureAction,NodeFailure,Inv1_R21_0_I0, ACKMessage
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next, ACKMessage


\* \*** Inv7971_R0_1_I2
\* THEOREM L_20 == TypeOK /\ Inv2345_R0_0_I2 /\ Inv10494_R0_1_I2 /\ Inv7971_R0_1_I2 /\ Next => Inv7971_R0_1_I2'
\*  <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
\*   \* (Inv7971_R0_1_I2,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv7971_R0_1_I2 /\ HRcvInvAction => Inv7971_R0_1_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv7971_R0_1_I2
\*   \* (Inv7971_R0_1_I2,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv7971_R0_1_I2 /\ HRcvInvNewerAction => Inv7971_R0_1_I2' 
\*     <2> SUFFICES ASSUME TypeOK /\ Inv7971_R0_1_I2 /\ HRcvInvNewerAction,
\*                         NEW VARI \in H_NODES',
\*                         NEW VARJ \in H_NODES'
\*                  PROVE  (~(VARI \in aliveNodes) \/ (~(nodeState[VARJ] = "valid") \/ (~(nodeTS[VARI].version < nodeTS[VARJ].version))))'
\*       BY DEF Inv7971_R0_1_I2
\*     <2> QED
\*       <3> SUFFICES ASSUME NEW n \in aliveNodes, NEW m \in msgsINV,
\*                           n \in aliveNodes,
\*                           m \in msgsINV,
\*                           m.type     = "INV",
\*                           m.epochID  = epochID,
\*                           m.sender  # n,
\*                           msgsACK' = msgsACK \cup {[type       |-> "ACK",
\*                                                     sender     |-> n,   
\*                                                     epochID    |-> epochID,
\*                                                     version    |-> m.version,
\*                                                     tieBreaker |-> m.tieBreaker]},
\*                           nodeLastWriter' = [nodeLastWriter EXCEPT ![n] = m.sender],
\*                           nodeTS' = [nodeTS EXCEPT ![n].version    = m.version, ![n].tieBreaker = m.tieBreaker],
\*                           IF nodeState[n] \in {"valid", "invalid", "replay"}
\*                                THEN 
\*                                nodeState' = [nodeState EXCEPT ![n] = "invalid"]
\*                                ELSE 
\*                                nodeState' = [nodeState EXCEPT ![n] = "invalid_write"],
\*                           UNCHANGED <<nodeLastWriteTS, aliveNodes, nodeRcvedAcks, epochID, nodeWriteEpochID, msgsVAL, msgsINV>>,
\*                           greaterTS(m.version, m.tieBreaker, nodeTS[n].version, nodeTS[n].tieBreaker)
\*                    PROVE  (~(VARI \in aliveNodes) \/ (~(nodeState[VARJ] = "valid") \/ (~(nodeTS[VARI].version < nodeTS[VARJ].version))))'
\*         BY DEF HRcvInvNewer, HRcvInvNewerAction
\*       <3>1. CASE (m.version) > (nodeTS[n].version)
\*         BY <3>1 DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv7971_R0_1_I2, ACKMessage, INVMessage
\*       <3>2. CASE /\   (m.version) = (nodeTS[n].version)
\*                  /\  (m.tieBreaker) > (nodeTS[n].tieBreaker)
\*         BY <3>2 DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv7971_R0_1_I2
\*       <3>3. QED
\*         BY <3>1, <3>2 DEF greaterTS
      
\*   \* (Inv7971_R0_1_I2,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv7971_R0_1_I2 /\ HFollowerWriteReplayAction => Inv7971_R0_1_I2' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv7971_R0_1_I2
\*   \* (Inv7971_R0_1_I2,HRcvValAction)
\*   <1>4. TypeOK /\ Inv2345_R0_0_I2 /\ Inv7971_R0_1_I2 /\ HRcvValAction => Inv7971_R0_1_I2' BY DEF TypeOK,Inv2345_R0_0_I2,HRcvValAction,HRcvVal,Inv7971_R0_1_I2
\*   \* (Inv7971_R0_1_I2,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv7971_R0_1_I2 /\ HCoordWriteReplayAction => Inv7971_R0_1_I2' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv7971_R0_1_I2
\*   \* (Inv7971_R0_1_I2,HWriteAction)
\*   <1>6. TypeOK /\ Inv7971_R0_1_I2 /\ HWriteAction => Inv7971_R0_1_I2' BY DEF TypeOK,HWriteAction,HWrite,Inv7971_R0_1_I2
\*   \* (Inv7971_R0_1_I2,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv7971_R0_1_I2 /\ HRcvAckAction => Inv7971_R0_1_I2' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv7971_R0_1_I2
\*   \* (Inv7971_R0_1_I2,HSendValsAction)
\*   <1>8. TypeOK /\ Inv10494_R0_1_I2 /\ Inv7971_R0_1_I2 /\ HSendValsAction => Inv7971_R0_1_I2' BY DEF TypeOK,Inv10494_R0_1_I2,HSendValsAction,HSendVals,Inv7971_R0_1_I2,receivedAllAcks,VALMessage
\*   \* (Inv7971_R0_1_I2,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv7971_R0_1_I2 /\ NodeFailureAction => Inv7971_R0_1_I2' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv7971_R0_1_I2
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv13944_R0_0_I2
\* THEOREM L_21 == TypeOK /\ Inv2345_R0_0_I2 /\ Inv10494_R0_1_I2 /\ Inv13944_R0_0_I2 /\ Next => Inv13944_R0_0_I2'
\*    <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
  
\*   \* (Inv13944_R0_0_I2,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv13944_R0_0_I2 /\ HRcvInvAction => Inv13944_R0_0_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv13944_R0_0_I2
\*   \* (Inv13944_R0_0_I2,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv13944_R0_0_I2 /\ HRcvInvNewerAction => Inv13944_R0_0_I2' 
\*     <2> SUFFICES ASSUME TypeOK /\ Inv13944_R0_0_I2 /\ HRcvInvNewerAction,
\*                         NEW VARI \in H_NODES',
\*                         NEW VARJ \in H_NODES'
\*                  PROVE  (~(VARJ \in aliveNodes) \/ (~(nodeState[VARI] = "valid")) \/ (~(nodeTS[VARI].version > nodeTS[VARJ].version)))'
\*       BY DEF Inv13944_R0_0_I2
\*     <2> QED
\*       <3> SUFFICES ASSUME NEW n \in aliveNodes, NEW m \in msgsINV,
\*                           HRcvInvNewer(n, m)
\*                    PROVE  (~(VARJ \in aliveNodes) \/ (~(nodeState[VARI] = "valid")) \/ (~(nodeTS[VARI].version > nodeTS[VARJ].version)))'
\*         BY DEF HRcvInvNewerAction
\*       <3> QED
\*         BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv13944_R0_0_I2, INVMessage, ACKMessage
      
\*   \* (Inv13944_R0_0_I2,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv13944_R0_0_I2 /\ HFollowerWriteReplayAction => Inv13944_R0_0_I2' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv13944_R0_0_I2
\*   \* (Inv13944_R0_0_I2,HRcvValAction)
\*   <1>4. TypeOK /\ Inv2345_R0_0_I2 /\ Inv13944_R0_0_I2 /\ HRcvValAction => Inv13944_R0_0_I2' BY DEF TypeOK,Inv2345_R0_0_I2,HRcvValAction,HRcvVal,Inv13944_R0_0_I2
\*   \* (Inv13944_R0_0_I2,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv13944_R0_0_I2 /\ HCoordWriteReplayAction => Inv13944_R0_0_I2' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv13944_R0_0_I2
\*   \* (Inv13944_R0_0_I2,HWriteAction)
\*   <1>6. TypeOK /\ Inv13944_R0_0_I2 /\ HWriteAction => Inv13944_R0_0_I2' BY DEF TypeOK,HWriteAction,HWrite,Inv13944_R0_0_I2
\*   \* (Inv13944_R0_0_I2,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv13944_R0_0_I2 /\ HRcvAckAction => Inv13944_R0_0_I2' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv13944_R0_0_I2
\*   \* (Inv13944_R0_0_I2,HSendValsAction)
\*   <1>8. TypeOK /\ Inv10494_R0_1_I2 /\ Inv13944_R0_0_I2 /\ HSendValsAction => Inv13944_R0_0_I2' BY DEF TypeOK,Inv10494_R0_1_I2,HSendValsAction,HSendVals,Inv13944_R0_0_I2,receivedAllAcks,VALMessage
\*   \* (Inv13944_R0_0_I2,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv13944_R0_0_I2 /\ NodeFailureAction => Inv13944_R0_0_I2' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv13944_R0_0_I2
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv13951_R0_0_I2
\* THEOREM L_22 == TypeOK /\ Inv3029_R2_0_I1 /\ Inv13951_R0_0_I2 /\ Next => Inv13951_R0_0_I2'
\*  <1> USE DEF greaterOrEqualTS, greaterTS, equalTS

\*   \* (Inv13951_R0_0_I2,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv13951_R0_0_I2 /\ HRcvInvAction => Inv13951_R0_0_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv13951_R0_0_I2
\*   \* (Inv13951_R0_0_I2,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv3029_R2_0_I1 /\ Inv13951_R0_0_I2 /\ HRcvInvNewerAction => Inv13951_R0_0_I2' BY DEF TypeOK,Inv3029_R2_0_I1,HRcvInvNewerAction,HRcvInvNewer,Inv13951_R0_0_I2
\*   \* (Inv13951_R0_0_I2,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv13951_R0_0_I2 /\ HFollowerWriteReplayAction => Inv13951_R0_0_I2' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv13951_R0_0_I2
\*   \* (Inv13951_R0_0_I2,HRcvValAction)
\*   <1>4. TypeOK /\ Inv13951_R0_0_I2 /\ HRcvValAction => Inv13951_R0_0_I2' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv13951_R0_0_I2
\*   \* (Inv13951_R0_0_I2,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv13951_R0_0_I2 /\ HCoordWriteReplayAction => Inv13951_R0_0_I2' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv13951_R0_0_I2
\*   \* (Inv13951_R0_0_I2,HWriteAction)
\*   <1>6. TypeOK /\ Inv13951_R0_0_I2 /\ HWriteAction => Inv13951_R0_0_I2' BY DEF TypeOK,HWriteAction,HWrite,Inv13951_R0_0_I2
\*   \* (Inv13951_R0_0_I2,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv13951_R0_0_I2 /\ HRcvAckAction => Inv13951_R0_0_I2' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv13951_R0_0_I2
\*   \* (Inv13951_R0_0_I2,HSendValsAction)
\*   <1>8. TypeOK /\ Inv13951_R0_0_I2 /\ HSendValsAction => Inv13951_R0_0_I2' BY DEF TypeOK,HSendValsAction,HSendVals,Inv13951_R0_0_I2,receivedAllAcks,VALMessage
\*   \* (Inv13951_R0_0_I2,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv13951_R0_0_I2 /\ NodeFailureAction => Inv13951_R0_0_I2' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv13951_R0_0_I2
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv4836_R0_1_I2
\* THEOREM L_23 == TypeOK /\ Inv3029_R2_0_I1 /\ Inv4836_R0_1_I2 /\ Next => Inv4836_R0_1_I2'
\* <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
\*   \* (Inv4836_R0_1_I2,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv4836_R0_1_I2 /\ HRcvInvAction => Inv4836_R0_1_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv4836_R0_1_I2
\*   \* (Inv4836_R0_1_I2,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv3029_R2_0_I1 /\ Inv4836_R0_1_I2 /\ HRcvInvNewerAction => Inv4836_R0_1_I2' BY DEF TypeOK,Inv3029_R2_0_I1,HRcvInvNewerAction,HRcvInvNewer,Inv4836_R0_1_I2
\*   \* (Inv4836_R0_1_I2,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv4836_R0_1_I2 /\ HFollowerWriteReplayAction => Inv4836_R0_1_I2' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv4836_R0_1_I2
\*   \* (Inv4836_R0_1_I2,HRcvValAction)
\*   <1>4. TypeOK /\ Inv4836_R0_1_I2 /\ HRcvValAction => Inv4836_R0_1_I2' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv4836_R0_1_I2
\*   \* (Inv4836_R0_1_I2,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv4836_R0_1_I2 /\ HCoordWriteReplayAction => Inv4836_R0_1_I2' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv4836_R0_1_I2
\*   \* (Inv4836_R0_1_I2,HWriteAction)
\*   <1>6. TypeOK /\ Inv4836_R0_1_I2 /\ HWriteAction => Inv4836_R0_1_I2' BY DEF TypeOK,HWriteAction,HWrite,Inv4836_R0_1_I2
\*   \* (Inv4836_R0_1_I2,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv4836_R0_1_I2 /\ HRcvAckAction => Inv4836_R0_1_I2' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv4836_R0_1_I2
\*   \* (Inv4836_R0_1_I2,HSendValsAction)
\*   <1>8. TypeOK /\ Inv4836_R0_1_I2 /\ HSendValsAction => Inv4836_R0_1_I2' BY DEF TypeOK,HSendValsAction,HSendVals,Inv4836_R0_1_I2,receivedAllAcks,VALMessage
\*   \* (Inv4836_R0_1_I2,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv4836_R0_1_I2 /\ NodeFailureAction => Inv4836_R0_1_I2' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv4836_R0_1_I2
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv890_R0_1_I2
\* THEOREM L_24 == TypeOK /\ Inv62_R15_1_I1 /\ Inv4085_R0_0_I2 /\ Inv2018_R0_0_I2 /\ Inv5_R0_1_I2 /\ Inv3025_R1_0_I2 /\ Inv890_R0_1_I2 /\ Next => Inv890_R0_1_I2'
  
\*   \* (Inv890_R0_1_I2,HRcvInvAction)
\*   <1> USE DEF receivedAllAcks
\*   <1>1. TypeOK /\ Inv890_R0_1_I2 /\ HRcvInvAction => Inv890_R0_1_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv890_R0_1_I2
\*   \* (Inv890_R0_1_I2,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv890_R0_1_I2 /\ HRcvInvNewerAction => Inv890_R0_1_I2' 
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv890_R0_1_I2,
\*                         TRUE,
\*                         NEW n \in aliveNodes, NEW m \in msgsINV,
\*                         n \in aliveNodes,
\*                         m \in msgsINV,
\*                         m.type     = "INV",
\*                         m.epochID  = epochID,
\*                         m.sender  # n,
\*                         msgsACK' = msgsACK \cup {[type       |-> "ACK",
\*                                                   sender     |-> n,   
\*                                                   epochID    |-> epochID,
\*                                                   version    |-> m.version,
\*                                                   tieBreaker |-> m.tieBreaker]},
\*                         nodeLastWriter' = [nodeLastWriter EXCEPT ![n] = m.sender],
\*                         nodeTS' = [nodeTS EXCEPT ![n].version    = m.version, ![n].tieBreaker = m.tieBreaker],
\*                         IF nodeState[n] \in {"valid", "invalid", "replay"}
\*                              THEN 
\*                              nodeState' = [nodeState EXCEPT ![n] = "invalid"]
\*                              ELSE 
\*                              nodeState' = [nodeState EXCEPT ![n] = "invalid_write"],
\*                         UNCHANGED <<nodeLastWriteTS, aliveNodes, nodeRcvedAcks, epochID, nodeWriteEpochID, msgsVAL, msgsINV>>,
\*                         NEW VARI \in H_NODES',
\*                         NEW VARJ \in H_NODES',
\*                         greaterTS(m.version, m.tieBreaker, nodeTS[n].version, nodeTS[n].tieBreaker)
\*                  PROVE  ((greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(nodeState[VARJ] = "valid")) \/ (~(receivedAllAcks(VARI) /\ nodeRcvedAcks = nodeRcvedAcks)))'
\*       BY DEF HRcvInvNewer, HRcvInvNewerAction, Inv890_R0_1_I2
\*     <2> USE DEF greaterOrEqualTS, greaterTS, equalTS
\*     <2>1. CASE (m.version) > (nodeTS[n].version)
\*       BY <2>1 DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv890_R0_1_I2
\*     <2>2. CASE /\   (m.version) = (nodeTS[n].version)
\*                /\  (m.tieBreaker) > (nodeTS[n].tieBreaker)
\*       BY <2>2 DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv890_R0_1_I2
\*     <2>3. QED
\*       BY <2>1, <2>2 DEF greaterTS
\*   \* (Inv890_R0_1_I2,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv890_R0_1_I2 /\ HFollowerWriteReplayAction => Inv890_R0_1_I2' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv890_R0_1_I2, greaterOrEqualTS, greaterTS, equalTS
\*   \* (Inv890_R0_1_I2,HRcvValAction)
\*   <1>4. TypeOK /\ Inv62_R15_1_I1 /\ Inv890_R0_1_I2 /\ HRcvValAction => Inv890_R0_1_I2' 
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv62_R15_1_I1,
\*                         Inv890_R0_1_I2,
\*                         TRUE,
\*                         NEW n \in aliveNodes, NEW m \in msgsVAL,
\*                         HRcvVal(n, m),
\*                         NEW VARI \in H_NODES',
\*                         NEW VARJ \in H_NODES'
\*                  PROVE  ((greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(nodeState[VARJ] = "valid")) \/ (~(receivedAllAcks(VARI) /\ nodeRcvedAcks = nodeRcvedAcks)))'
\*       BY DEF HRcvValAction, Inv890_R0_1_I2
\*     <2> USE DEF greaterOrEqualTS, greaterTS, equalTS
\*     <2> QED
\*       BY FS_Subset, FS_Singleton DEF TypeOK,Inv62_R15_1_I1,HRcvValAction,HRcvVal,Inv890_R0_1_I2
\*   \* (Inv890_R0_1_I2,HCoordWriteReplayAction)
\*   <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
\*   <1>5. TypeOK /\ Inv890_R0_1_I2 /\ HCoordWriteReplayAction => Inv890_R0_1_I2' 
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv890_R0_1_I2,
\*                         TRUE,
\*                         NEW n \in aliveNodes,
\*                         HCoordWriteReplay(n),
\*                         NEW VARI \in H_NODES',
\*                         NEW VARJ \in H_NODES'
\*                  PROVE  ((greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(nodeState[VARJ] = "valid")) \/ (~(receivedAllAcks(VARI) /\ nodeRcvedAcks = nodeRcvedAcks)))'
\*       BY DEF HCoordWriteReplayAction, Inv890_R0_1_I2
\*     <2> QED
\*       BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv890_R0_1_I2
\*   \* (Inv890_R0_1_I2,HWriteAction)
\*   <1>6. TypeOK /\ Inv890_R0_1_I2 /\ HWriteAction => Inv890_R0_1_I2' 
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv890_R0_1_I2,
\*                         TRUE,
\*                         NEW n \in aliveNodes,
\*                         HWrite(n),
\*                         NEW VARI \in H_NODES',
\*                         NEW VARJ \in H_NODES'
\*                  PROVE  ((greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(nodeState[VARJ] = "valid")) \/ (~(receivedAllAcks(VARI) /\ nodeRcvedAcks = nodeRcvedAcks)))'
\*       BY DEF HWriteAction, Inv890_R0_1_I2
\*     <2> QED
\*       BY DEF TypeOK,HWriteAction,HWrite,Inv890_R0_1_I2
\*   \* (Inv890_R0_1_I2,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv4085_R0_0_I2 /\ Inv2018_R0_0_I2 /\ Inv890_R0_1_I2 /\ HRcvAckAction => Inv890_R0_1_I2' BY DEF TypeOK,Inv4085_R0_0_I2,Inv2018_R0_0_I2,HRcvAckAction,HRcvAck,Inv890_R0_1_I2
\*   \* (Inv890_R0_1_I2,HSendValsAction)
\*   <1>8. TypeOK /\ Inv5_R0_1_I2 /\ Inv3025_R1_0_I2 /\ Inv890_R0_1_I2 /\ HSendValsAction => Inv890_R0_1_I2' BY DEF TypeOK,Inv5_R0_1_I2,Inv3025_R1_0_I2,HSendValsAction,HSendVals,Inv890_R0_1_I2,receivedAllAcks,VALMessage
\*   \* (Inv890_R0_1_I2,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv890_R0_1_I2 /\ NodeFailureAction => Inv890_R0_1_I2' 
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv890_R0_1_I2,
\*                         TRUE,
\*                         NEW n \in aliveNodes,
\*                         NodeFailure(n),
\*                         NEW VARI \in H_NODES',
\*                         NEW VARJ \in H_NODES'
\*                  PROVE  ((greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(nodeState[VARJ] = "valid")) \/ (~(receivedAllAcks(VARI) /\ nodeRcvedAcks = nodeRcvedAcks)))'
\*       BY DEF Inv890_R0_1_I2, NodeFailureAction
\*     <2> QED
\*       BY FS_Subset, FS_Singleton DEF TypeOK,NodeFailureAction,NodeFailure,Inv890_R0_1_I2
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv62_R15_1_I1
\* THEOREM L_25 == TypeOK /\ Inv2345_R0_0_I2 /\ Inv1_R21_0_I0 /\ Inv5_R0_1_I2 /\ Inv3025_R1_0_I2 /\ Inv62_R15_1_I1 /\ Next => Inv62_R15_1_I1'
\*   <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
\*   \* (Inv62_R15_1_I1,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv62_R15_1_I1 /\ HRcvInvAction => Inv62_R15_1_I1' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv62_R15_1_I1
\*   \* (Inv62_R15_1_I1,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv62_R15_1_I1 /\ HRcvInvNewerAction => Inv62_R15_1_I1' BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv62_R15_1_I1
\*   \* (Inv62_R15_1_I1,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv62_R15_1_I1 /\ HFollowerWriteReplayAction => Inv62_R15_1_I1' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv62_R15_1_I1
\*   \* (Inv62_R15_1_I1,HRcvValAction)
\*   <1>4. TypeOK /\ Inv62_R15_1_I1 /\ HRcvValAction => Inv62_R15_1_I1' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv62_R15_1_I1
\*   \* (Inv62_R15_1_I1,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv62_R15_1_I1 /\ HCoordWriteReplayAction => Inv62_R15_1_I1' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv62_R15_1_I1
\*   \* (Inv62_R15_1_I1,HWriteAction)
\*   <1>6. TypeOK /\ Inv62_R15_1_I1 /\ HWriteAction => Inv62_R15_1_I1' BY DEF TypeOK,HWriteAction,HWrite,Inv62_R15_1_I1
\*   \* (Inv62_R15_1_I1,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv2345_R0_0_I2 /\ Inv1_R21_0_I0 /\ Inv62_R15_1_I1 /\ HRcvAckAction => Inv62_R15_1_I1' BY DEF TypeOK,Inv2345_R0_0_I2,Inv1_R21_0_I0,HRcvAckAction,HRcvAck,Inv62_R15_1_I1
\*   \* (Inv62_R15_1_I1,HSendValsAction)
\*   <1>8. TypeOK /\ Inv5_R0_1_I2 /\ Inv3025_R1_0_I2 /\ Inv62_R15_1_I1 /\ HSendValsAction => Inv62_R15_1_I1' 
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv5_R0_1_I2,
\*                         Inv3025_R1_0_I2,
\*                         Inv62_R15_1_I1,
\*                         TRUE,
\*                         NEW n \in aliveNodes,
\*                         HSendVals(n),
\*                         NEW VARI \in H_NODES',
\*                         NEW VARJ \in H_NODES',
\*                         NEW VARMVALI \in msgsVAL'
\*                  PROVE  (~(VARJ \in nodeRcvedAcks[VARI]) \/ (~(greaterTS(VARMVALI.version, VARMVALI.tieBreaker, nodeTS[VARI].version, nodeTS[VARI].tieBreaker))))'
\*       BY DEF HSendValsAction, Inv62_R15_1_I1
\*     <2> QED
\*       BY FS_Subset, FS_Singleton DEF TypeOK,Inv5_R0_1_I2,Inv3025_R1_0_I2,HSendValsAction,HSendVals,Inv62_R15_1_I1,receivedAllAcks,VALMessage
\*   \* (Inv62_R15_1_I1,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv62_R15_1_I1 /\ NodeFailureAction => Inv62_R15_1_I1' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv62_R15_1_I1
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* \*** Inv618_R0_1_I2
\* THEOREM L_26 == TypeOK /\ Inv627_R9_0_I2 /\ Inv1666_R10_0_I1 /\ Inv4_R0_1_I2 /\ Inv2018_R0_0_I2 /\ Inv618_R0_1_I2 /\ Next => Inv618_R0_1_I2'
\*   <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
\*   \* (Inv618_R0_1_I2,HRcvInvAction)
\*   <1>1. TypeOK /\ Inv618_R0_1_I2 /\ HRcvInvAction => Inv618_R0_1_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv618_R0_1_I2
\*   \* (Inv618_R0_1_I2,HRcvInvNewerAction)
\*   <1>2. TypeOK /\ Inv618_R0_1_I2 /\ HRcvInvNewerAction => Inv618_R0_1_I2' 
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv618_R0_1_I2,
\*                         TRUE,
\*                         NEW n \in aliveNodes, NEW m \in msgsINV,
\*                         n \in aliveNodes,
\*                         m \in msgsINV,
\*                         m.type     = "INV",
\*                         m.epochID  = epochID,
\*                         m.sender  # n,
\*                         msgsACK' = msgsACK \cup {[type       |-> "ACK",
\*                                                   sender     |-> n,   
\*                                                   epochID    |-> epochID,
\*                                                   version    |-> m.version,
\*                                                   tieBreaker |-> m.tieBreaker]},
\*                         nodeLastWriter' = [nodeLastWriter EXCEPT ![n] = m.sender],
\*                         nodeTS' = [nodeTS EXCEPT ![n].version    = m.version, ![n].tieBreaker = m.tieBreaker],
\*                         IF nodeState[n] \in {"valid", "invalid", "replay"}
\*                              THEN 
\*                              nodeState' = [nodeState EXCEPT ![n] = "invalid"]
\*                              ELSE 
\*                              nodeState' = [nodeState EXCEPT ![n] = "invalid_write"],
\*                         UNCHANGED <<nodeLastWriteTS, aliveNodes, nodeRcvedAcks, epochID, nodeWriteEpochID, msgsVAL, msgsINV>>,
\*                         NEW VARI \in H_NODES',
\*                         NEW VARJ \in H_NODES',
\*                         greaterTS(m.version, m.tieBreaker, nodeTS[n].version, nodeTS[n].tieBreaker)
\*                  PROVE  ((greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(nodeState[VARJ] = "write")) \/ (~(VARI \in nodeRcvedAcks[VARJ])))'
\*       BY DEF HRcvInvNewer, HRcvInvNewerAction, Inv618_R0_1_I2
\*     <2>1. CASE (m.version) > (nodeTS[n].version)
\*       BY <2>1 DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv618_R0_1_I2, ACKMessage
\*     <2>2. CASE /\   (m.version) = (nodeTS[n].version)
\*                /\  (m.tieBreaker) > (nodeTS[n].tieBreaker)
\*       BY <2>2 DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv618_R0_1_I2, ACKMessage
\*     <2>3. QED
\*       BY <2>1, <2>2 DEF greaterTS
\*   \* (Inv618_R0_1_I2,HFollowerWriteReplayAction)
\*   <1>3. TypeOK /\ Inv618_R0_1_I2 /\ HFollowerWriteReplayAction => Inv618_R0_1_I2' 
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv618_R0_1_I2,
\*                         TRUE,
\*                         NEW n \in aliveNodes,
\*                         HFollowerWriteReplay(n),
\*                         NEW VARI \in H_NODES',
\*                         NEW VARJ \in H_NODES'
\*                  PROVE  ((greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(nodeState[VARJ] = "write")) \/ (~(VARI \in nodeRcvedAcks[VARJ])))'
\*       BY DEF HFollowerWriteReplayAction, Inv618_R0_1_I2
\*     <2> QED
\*       BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv618_R0_1_I2
\*   \* (Inv618_R0_1_I2,HRcvValAction)
\*   <1>4. TypeOK /\ Inv618_R0_1_I2 /\ HRcvValAction => Inv618_R0_1_I2' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv618_R0_1_I2
\*   \* (Inv618_R0_1_I2,HCoordWriteReplayAction)
\*   <1>5. TypeOK /\ Inv618_R0_1_I2 /\ HCoordWriteReplayAction => Inv618_R0_1_I2' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv618_R0_1_I2
\*   \* (Inv618_R0_1_I2,HWriteAction)
\*   <1>6. TypeOK /\ Inv618_R0_1_I2 /\ HWriteAction => Inv618_R0_1_I2' 
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv618_R0_1_I2,
\*                         TRUE,
\*                         NEW n \in aliveNodes,
\*                         HWrite(n),
\*                         NEW VARI \in H_NODES',
\*                         NEW VARJ \in H_NODES'
\*                  PROVE  ((greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(nodeState[VARJ] = "write")) \/ (~(VARI \in nodeRcvedAcks[VARJ])))'
\*       BY DEF HWriteAction, Inv618_R0_1_I2
\*     <2> QED
\*       BY FS_Subset, FS_Singleton DEF TypeOK,HWriteAction,HWrite,Inv618_R0_1_I2
\*   \* (Inv618_R0_1_I2,HRcvAckAction)
\*   <1>7. TypeOK /\ Inv627_R9_0_I2 /\ Inv1666_R10_0_I1 /\ Inv4_R0_1_I2 /\ Inv2018_R0_0_I2 /\ Inv618_R0_1_I2 /\ HRcvAckAction => Inv618_R0_1_I2' 
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv627_R9_0_I2,
\*                         Inv1666_R10_0_I1,
\*                         Inv4_R0_1_I2,
\*                         Inv2018_R0_0_I2,
\*                         Inv618_R0_1_I2,
\*                         TRUE,
\*                         NEW n \in aliveNodes, NEW m \in msgsACK,
\*                         HRcvAck(n, m),
\*                         NEW VARI \in H_NODES',
\*                         NEW VARJ \in H_NODES'
\*                  PROVE  ((greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(nodeState[VARJ] = "write")) \/ (~(VARI \in nodeRcvedAcks[VARJ])))'
\*       BY DEF HRcvAckAction, Inv618_R0_1_I2
\*     <2> QED
\*       BY FS_Subset, FS_Singleton, FS_Union, FS_Difference DEF TypeOK,Inv627_R9_0_I2,Inv1666_R10_0_I1,Inv4_R0_1_I2,Inv2018_R0_0_I2,HRcvAckAction,HRcvAck,Inv618_R0_1_I2
\*   \* (Inv618_R0_1_I2,HSendValsAction)
\*   <1>8. TypeOK /\ Inv618_R0_1_I2 /\ HSendValsAction => Inv618_R0_1_I2' BY DEF TypeOK,HSendValsAction,HSendVals,Inv618_R0_1_I2,receivedAllAcks,VALMessage
\*   \* (Inv618_R0_1_I2,NodeFailureAction)
\*   <1>9. TypeOK /\ Inv618_R0_1_I2 /\ NodeFailureAction => Inv618_R0_1_I2' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv618_R0_1_I2
\* <1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next

\* \* Initiation.
\* THEOREM Init => IndGlobal
\*     <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
\*     <1>0. Init => TypeOK 
\*       <2> SUFFICES ASSUME Init
\*                    PROVE  TypeOK
\*         OBVIOUS
\*       <2>1. msgsINV \subseteq INVMessage
\*         BY DEF Init, TypeOK, IndGlobal, INVMessage, VALMessage, ACKMessage
\*       <2>2. msgsVAL \subseteq VALMessage
\*         BY DEF Init, TypeOK, IndGlobal, INVMessage, VALMessage, ACKMessage
\*       <2>3. msgsACK \subseteq ACKMessage
\*         BY DEF Init, TypeOK, IndGlobal, INVMessage, VALMessage, ACKMessage
\*       <2>4. nodeRcvedAcks \in [H_NODES -> SUBSET H_NODES]
\*         BY DEF Init, TypeOK, IndGlobal, INVMessage, VALMessage, ACKMessage
\*       <2>5. \A n \in H_NODES: nodeRcvedAcks[n] \subseteq (H_NODES \ {n})
\*         BY DEF Init, TypeOK, IndGlobal, INVMessage, VALMessage, ACKMessage
\*       <2>6. nodeLastWriter  \in [H_NODES -> H_NODES]
\*         BY DEF Init, TypeOK, IndGlobal, INVMessage, VALMessage, ACKMessage
\*       <2>7. nodeLastWriteTS \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]]
\*         BY DEF Init, TypeOK, IndGlobal, INVMessage, VALMessage, ACKMessage
\*       <2>8. nodeTS          \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]]
\*         BY DEF Init, TypeOK, IndGlobal, INVMessage, VALMessage, ACKMessage
\*       <2>9. nodeState       \in [H_NODES -> {"valid", "invalid", "invalid_write", "write", "replay"}]
\*         BY DEF Init, TypeOK, IndGlobal, INVMessage, VALMessage, ACKMessage
\*       <2>10. aliveNodes      \in SUBSET H_NODES
\*         BY DEF Init, TypeOK, IndGlobal, INVMessage, VALMessage, ACKMessage
\*       <2>11. epochID         \in Nat
\*         BY DEF Init, TypeOK, IndGlobal, INVMessage, VALMessage, ACKMessage
\*       <2>12. nodeWriteEpochID \in [H_NODES -> Nat]
\*         BY DEF Init, TypeOK, IndGlobal, INVMessage, VALMessage, ACKMessage
\*       <2>13. QED
\*         BY <2>1, <2>10, <2>11, <2>12, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
\*     <1>1. Init => Safety BY DEF Init, Safety, IndGlobal, HConsistent
\*     <1>2. Init => Inv2345_R0_0_I2 BY DEF Init, Inv2345_R0_0_I2, IndGlobal
\*     <1>3. Init => Inv10494_R0_1_I2 BY DEF Init, Inv10494_R0_1_I2, IndGlobal
\*     <1>4. Init => Inv627_R9_0_I2 BY DEF Init, Inv627_R9_0_I2, IndGlobal
\*     <1>5. Init => Inv5_R0_1_I2 BY DEF Init, Inv5_R0_1_I2, IndGlobal
\*     <1>6. Init => Inv3096_R0_0_I2 BY DEF Init, Inv3096_R0_0_I2, IndGlobal
\*     <1>7. Init => Inv29_R2_0_I1 BY DEF Init, Inv29_R2_0_I1, IndGlobal
\*     <1>8. Init => Inv14828_R0_0_I2 BY DEF Init, Inv14828_R0_0_I2, IndGlobal
\*     <1>9. Init => Inv3029_R2_0_I1 BY DEF Init, Inv3029_R2_0_I1, IndGlobal
\*     <1>10. Init => Inv548_R0_1_I2 BY DEF Init, Inv548_R0_1_I2, IndGlobal
\*     <1>11. Init => Inv2701_R0_0_I2 BY DEF Init, Inv2701_R0_0_I2, IndGlobal
\*     <1>12. Init => Inv4085_R0_0_I2 BY DEF Init, Inv4085_R0_0_I2, IndGlobal
\*     <1>13. Init => Inv3025_R1_0_I2 BY DEF Init, Inv3025_R1_0_I2, IndGlobal
\*     <1>14. Init => Inv1666_R10_0_I1 BY DEF Init, Inv1666_R10_0_I1, IndGlobal
\*     <1>15. Init => Inv28_R17_0_I1 BY DEF Init, Inv28_R17_0_I1, IndGlobal
\*     <1>16. Init => Inv2018_R0_0_I2 BY DEF Init, Inv2018_R0_0_I2, IndGlobal
\*     <1>17. Init => Inv4_R0_1_I2 BY DEF Init, Inv4_R0_1_I2, IndGlobal
\*     <1>18. Init => Inv927_R9_0_I2 BY DEF Init, Inv927_R9_0_I2, IndGlobal
\*     <1>19. Init => Inv1_R21_0_I0 BY DEF Init, Inv1_R21_0_I0, IndGlobal
\*     <1>20. Init => Inv7971_R0_1_I2 BY DEF Init, Inv7971_R0_1_I2, IndGlobal
\*     <1>21. Init => Inv13944_R0_0_I2 BY DEF Init, Inv13944_R0_0_I2, IndGlobal
\*     <1>22. Init => Inv13951_R0_0_I2 BY DEF Init, Inv13951_R0_0_I2, IndGlobal
\*     <1>23. Init => Inv4836_R0_1_I2 BY DEF Init, Inv4836_R0_1_I2, IndGlobal
\*     <1>24. Init => Inv890_R0_1_I2 BY DEF Init, Inv890_R0_1_I2, IndGlobal
\*     <1>25. Init => Inv62_R15_1_I1 BY DEF Init, Inv62_R15_1_I1, IndGlobal
\*     <1>26. Init => Inv618_R0_1_I2 BY DEF Init, Inv618_R0_1_I2, IndGlobal
\*     <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14,<1>15,<1>16,<1>17,<1>18,<1>19,<1>20,<1>21,<1>22,<1>23,<1>24,<1>25,<1>26 DEF IndGlobal

\* \* Consecution.
\* THEOREM IndGlobal /\ Next => IndGlobal'
\*   BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13,L_14,L_15,L_16,L_17,L_18,L_19,L_20,L_21,L_22,L_23,L_24,L_25,L_26 DEF Next, IndGlobal







\* Proof Graph Stats
\* ==================
\* seed: 7
\* num proof graph nodes: 8
\* num proof obligations: 72
Safety == HConsistent
Inv16269_aa90_R0_0_I2 == \A VARI \in H_NODES : \A VARJ \in H_NODES : (nodeTS[VARI] = nodeTS[VARJ]) \/ (~(greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(nodeTS[VARI].tieBreaker = VARJ)))
Inv2349_4d16_R0_0_I2 == \A VARI \in H_NODES : \A VARMVALI \in msgsVAL : ~(VARI \in aliveNodes) \/ (~(greaterTS(VARMVALI.version, VARMVALI.tieBreaker, nodeTS[VARI].version, nodeTS[VARI].tieBreaker)))
Inv2065_94b3_R0_0_I2 == \A VARI \in H_NODES : \A VARJ \in H_NODES : (greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(VARI \in aliveNodes)) \/ (~(nodeState[VARJ] = "valid"))
Inv2586_f463_R0_1_I2 == \A VARI \in H_NODES : \A VARJ \in H_NODES : (greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(VARI \in nodeRcvedAcks[VARJ])) \/ (~(nodeState[VARJ] \in {"write", "replay"}))
Inv3257_59f9_R1_0_I1 == \A VARI \in H_NODES : \A VARMINVI \in msgsINV : ~(VARMINVI.tieBreaker = VARI) \/ (~(greaterTS(VARMINVI.version, VARMINVI.tieBreaker, nodeTS[VARI].version, nodeTS[VARI].tieBreaker)))
Inv2796_9992_R4_0_I1 == \A VARI \in H_NODES : (nodeTS[VARI] = nodeLastWriteTS[VARI]) \/ (~(nodeState[VARI] \in {"write", "replay"}))
Inv3739_c35e_R4_0_I1 == \A VARI \in H_NODES : \A VARMACKI \in msgsACK : ~(VARMACKI.sender = VARI) \/ (~(greaterTS(VARMACKI.version, VARMACKI.tieBreaker, nodeTS[VARI].version, nodeTS[VARI].tieBreaker)))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv16269_aa90_R0_0_I2
  /\ Inv3257_59f9_R1_0_I1
  /\ Inv2349_4d16_R0_0_I2
  /\ Inv2586_f463_R0_1_I2
  /\ Inv2796_9992_R4_0_I1
  /\ Inv3739_c35e_R4_0_I1
  /\ Inv2065_94b3_R0_0_I2


\* mean in-degree: 1.625
\* median in-degree: 2
\* max in-degree: 5
\* min in-degree: 0
\* mean variable slice size: 0

ASSUME A0 == IsFiniteSet(H_NODES) /\ H_NODES \subseteq Nat /\ H_NODES # {} /\ H_MAX_VERSION \in Nat /\ \E k \in H_NODES : \A m \in H_NODES : k =< m /\ H_NODES = {0}
USE A0
USE DEF INVMessage, ACKMessage, VALMessage
USE FS_Subset, FS_Singleton

\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  <1>. USE A0
  \* (TypeOK,HRcvInvAction)
  <1>1. TypeOK /\ TypeOK /\ HRcvInvAction => TypeOK' BY DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
  \* (TypeOK,HRcvInvNewerAction)
  <1>2. TypeOK /\ TypeOK /\ HRcvInvNewerAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ HRcvInvNewerAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (msgsINV \subseteq INVMessage)'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>2. (msgsVAL \subseteq VALMessage)'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>3. (msgsACK \subseteq ACKMessage)'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>4. (nodeRcvedAcks \in [H_NODES -> SUBSET H_NODES])'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>5. (\A n \in H_NODES: nodeRcvedAcks[n] \subseteq (H_NODES \ {n}))'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>6. (nodeLastWriter  \in [H_NODES -> H_NODES])'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>7. (nodeLastWriteTS \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]])'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>8. (nodeTS          \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]])'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>9. (nodeState       \in [H_NODES -> {"valid", "invalid", "invalid_write", "write", "replay"}])'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>10. (aliveNodes      \in SUBSET H_NODES)'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>11. (epochID         \in Nat)'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>12. (nodeWriteEpochID \in [H_NODES -> Nat])'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>13. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
  \* (TypeOK,HFollowerWriteReplayAction)
  <1>3. TypeOK /\ TypeOK /\ HFollowerWriteReplayAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ HFollowerWriteReplayAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (msgsINV \subseteq INVMessage)'
      BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,TypeOK
    <2>2. (msgsVAL \subseteq VALMessage)'
      BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,TypeOK
    <2>3. (msgsACK \subseteq ACKMessage)'
      BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,TypeOK
    <2>4. (nodeRcvedAcks \in [H_NODES -> SUBSET H_NODES])'
      BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,TypeOK
    <2>5. (\A n \in H_NODES: nodeRcvedAcks[n] \subseteq (H_NODES \ {n}))'
      BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,TypeOK
    <2>6. (nodeLastWriter  \in [H_NODES -> H_NODES])'
      BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,TypeOK
    <2>7. (nodeLastWriteTS \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]])'
      BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,TypeOK
    <2>8. (nodeTS          \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]])'
      BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,TypeOK
    <2>9. (nodeState       \in [H_NODES -> {"valid", "invalid", "invalid_write", "write", "replay"}])'
      BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,TypeOK
    <2>10. (aliveNodes      \in SUBSET H_NODES)'
      BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,TypeOK
    <2>11. (epochID         \in Nat)'
      BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,TypeOK
    <2>12. (nodeWriteEpochID \in [H_NODES -> Nat])'
      BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,TypeOK
    <2>13. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
  \* (TypeOK,HRcvValAction)
  <1>4. TypeOK /\ TypeOK /\ HRcvValAction => TypeOK' BY DEF TypeOK,HRcvValAction,HRcvVal,TypeOK
  \* (TypeOK,HCoordWriteReplayAction)
  <1>5. TypeOK /\ TypeOK /\ HCoordWriteReplayAction => TypeOK' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,TypeOK
  \* (TypeOK,HWriteAction)
  <1>6. TypeOK /\ TypeOK /\ HWriteAction => TypeOK' BY DEF TypeOK,HWriteAction,HWrite,TypeOK
  \* (TypeOK,HRcvAckAction)
  <1>7. TypeOK /\ TypeOK /\ HRcvAckAction => TypeOK' BY DEF TypeOK,HRcvAckAction,HRcvAck,TypeOK
  \* (TypeOK,HSendValsAction)
  <1>8. TypeOK /\ TypeOK /\ HSendValsAction => TypeOK' BY DEF TypeOK,HSendValsAction,HSendVals,TypeOK,receivedAllAcks,VALMessage
  \* (TypeOK,NodeFailureAction)
  <1>9. TypeOK /\ TypeOK /\ NodeFailureAction => TypeOK' BY DEF TypeOK,NodeFailureAction,NodeFailure,TypeOK
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Inv16269_aa90_R0_0_I2 /\ Inv2349_4d16_R0_0_I2 /\ Inv2065_94b3_R0_0_I2 /\ Inv2586_f463_R0_1_I2 /\ Inv2065_94b3_R0_0_I2 /\ Safety /\ Next => Safety'
  <1>. USE A0
  <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
  
  \* (Safety,HRcvInvAction)
  <1>1. TypeOK /\ Safety /\ HRcvInvAction => Safety' BY DEF TypeOK,HRcvInvAction,HRcvInv,Safety,HConsistent
  \* (Safety,HRcvInvNewerAction)
  <1>2. TypeOK /\ Safety /\ HRcvInvNewerAction => Safety' BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Safety,HConsistent
  \* (Safety,HFollowerWriteReplayAction)
  <1>3. TypeOK /\ Safety /\ HFollowerWriteReplayAction => Safety' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Safety,HConsistent
  \* (Safety,HRcvValAction)
  <1>4. TypeOK /\ Inv16269_aa90_R0_0_I2 /\ Inv2349_4d16_R0_0_I2 /\ Inv2065_94b3_R0_0_I2 /\ Safety /\ HRcvValAction => Safety' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv16269_aa90_R0_0_I2,
                        Inv2349_4d16_R0_0_I2,
                        Inv2065_94b3_R0_0_I2,
                        Safety,
                        TRUE,
                        NEW n \in aliveNodes, NEW m \in msgsVAL,
                        HRcvVal(n, m)
                 PROVE  Safety'
      BY DEF HRcvValAction
    <2> QED
      BY DEF TypeOK,Inv16269_aa90_R0_0_I2,Inv2349_4d16_R0_0_I2,Inv2065_94b3_R0_0_I2,HRcvValAction,HRcvVal,Safety,HConsistent
  \* (Safety,HCoordWriteReplayAction)
  <1>5. TypeOK /\ Safety /\ HCoordWriteReplayAction => Safety' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Safety,HConsistent
  \* (Safety,HWriteAction)
  <1>6. TypeOK /\ Safety /\ HWriteAction => Safety' BY DEF TypeOK,HWriteAction,HWrite,Safety,HConsistent
  \* (Safety,HRcvAckAction)
  <1>7. TypeOK /\ Safety /\ HRcvAckAction => Safety' 
    <2> SUFFICES ASSUME TypeOK,
                        Safety,
                        TRUE,
                        NEW n \in aliveNodes, NEW m \in msgsACK,
                        HRcvAck(n, m)
                 PROVE  Safety'
      BY DEF HRcvAckAction
    <2> QED
      BY DEF TypeOK,HRcvAckAction,HRcvAck,Safety,HConsistent
  \* (Safety,HSendValsAction)
  <1>8. TypeOK /\ Inv2586_f463_R0_1_I2 /\ Inv2065_94b3_R0_0_I2 /\ Safety /\ HSendValsAction => Safety' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv2586_f463_R0_1_I2,
                        Inv2065_94b3_R0_0_I2,
                        Safety,
                        TRUE,
                        NEW n \in aliveNodes,
                        HSendVals(n)
                 PROVE  Safety'
      BY DEF HSendValsAction
    <2> QED
      BY DEF TypeOK,Inv2586_f463_R0_1_I2,Inv2065_94b3_R0_0_I2,HSendValsAction,HSendVals,Safety,receivedAllAcks,VALMessage,HConsistent
  \* (Safety,NodeFailureAction)
  <1>9. TypeOK /\ Safety /\ NodeFailureAction => Safety' BY DEF TypeOK,NodeFailureAction,NodeFailure,Safety,HConsistent
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next

USE DEF greaterOrEqualTS, greaterTS, equalTS

\*** Inv16269_aa90_R0_0_I2
THEOREM L_2 == TypeOK /\ Inv3257_59f9_R1_0_I1 /\ Inv16269_aa90_R0_0_I2 /\ Next => Inv16269_aa90_R0_0_I2'
  <1>. USE A0
    <1> USE DEF greaterOrEqualTS, greaterTS, equalTS
  
  \* (Inv16269_aa90_R0_0_I2,HRcvInvAction)
  <1>1. TypeOK /\ Inv16269_aa90_R0_0_I2 /\ HRcvInvAction => Inv16269_aa90_R0_0_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv16269_aa90_R0_0_I2
  \* (Inv16269_aa90_R0_0_I2,HRcvInvNewerAction)
  <1>2. TypeOK /\ Inv3257_59f9_R1_0_I1 /\ Inv16269_aa90_R0_0_I2 /\ HRcvInvNewerAction => Inv16269_aa90_R0_0_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv3257_59f9_R1_0_I1,
                        Inv16269_aa90_R0_0_I2,
                        TRUE,
                        NEW n \in aliveNodes, NEW m \in msgsINV,
                        n \in aliveNodes,
                        m \in msgsINV,
                        m.type     = "INV",
                        m.epochID  = epochID,
                        m.sender  # n,
                        msgsACK' = msgsACK \cup {[type       |-> "ACK",
                                                  sender     |-> n,   
                                                  epochID    |-> epochID,
                                                  version    |-> m.version,
                                                  tieBreaker |-> m.tieBreaker]},
                        nodeLastWriter' = [nodeLastWriter EXCEPT ![n] = m.sender],
                        nodeTS' = [nodeTS EXCEPT ![n].version    = m.version, ![n].tieBreaker = m.tieBreaker],
                        IF nodeState[n] \in {"valid", "invalid", "replay"}
                             THEN 
                             nodeState' = [nodeState EXCEPT ![n] = "invalid"]
                             ELSE 
                             nodeState' = [nodeState EXCEPT ![n] = "invalid_write"],
                        UNCHANGED <<nodeLastWriteTS, aliveNodes, nodeRcvedAcks, epochID, nodeWriteEpochID, msgsVAL, msgsINV>>,
                        NEW VARI \in H_NODES',
                        NEW VARJ \in H_NODES',
                        greaterTS(m.version, m.tieBreaker, nodeTS[n].version, nodeTS[n].tieBreaker)
                 PROVE  ((nodeTS[VARI] = nodeTS[VARJ]) \/ (~(greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(nodeTS[VARI].tieBreaker = VARJ))))'
      BY DEF HRcvInvNewer, HRcvInvNewerAction, Inv16269_aa90_R0_0_I2
    <2>1. CASE (m.version) > (nodeTS[n].version)
      BY <2>1 DEF TypeOK,Inv3257_59f9_R1_0_I1,HRcvInvNewerAction,HRcvInvNewer,Inv16269_aa90_R0_0_I2
    <2>2. CASE /\   (m.version) = (nodeTS[n].version)
               /\  (m.tieBreaker) > (nodeTS[n].tieBreaker)
      BY <2>2 DEF TypeOK,Inv3257_59f9_R1_0_I1,HRcvInvNewerAction,HRcvInvNewer,Inv16269_aa90_R0_0_I2
    <2>3. QED
      BY <2>1, <2>2 DEF greaterTS
  \* (Inv16269_aa90_R0_0_I2,HFollowerWriteReplayAction)
  <1>3. TypeOK /\ Inv16269_aa90_R0_0_I2 /\ HFollowerWriteReplayAction => Inv16269_aa90_R0_0_I2' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv16269_aa90_R0_0_I2
  \* (Inv16269_aa90_R0_0_I2,HRcvValAction)
  <1>4. TypeOK /\ Inv16269_aa90_R0_0_I2 /\ HRcvValAction => Inv16269_aa90_R0_0_I2' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv16269_aa90_R0_0_I2
  \* (Inv16269_aa90_R0_0_I2,HCoordWriteReplayAction)
  <1>5. TypeOK /\ Inv16269_aa90_R0_0_I2 /\ HCoordWriteReplayAction => Inv16269_aa90_R0_0_I2' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv16269_aa90_R0_0_I2
  \* (Inv16269_aa90_R0_0_I2,HWriteAction)
  <1>6. TypeOK /\ Inv16269_aa90_R0_0_I2 /\ HWriteAction => Inv16269_aa90_R0_0_I2' BY DEF TypeOK,HWriteAction,HWrite,Inv16269_aa90_R0_0_I2
  \* (Inv16269_aa90_R0_0_I2,HRcvAckAction)
  <1>7. TypeOK /\ Inv16269_aa90_R0_0_I2 /\ HRcvAckAction => Inv16269_aa90_R0_0_I2' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv16269_aa90_R0_0_I2
  \* (Inv16269_aa90_R0_0_I2,HSendValsAction)
  <1>8. TypeOK /\ Inv16269_aa90_R0_0_I2 /\ HSendValsAction => Inv16269_aa90_R0_0_I2' BY DEF TypeOK,HSendValsAction,HSendVals,Inv16269_aa90_R0_0_I2,receivedAllAcks,VALMessage
  \* (Inv16269_aa90_R0_0_I2,NodeFailureAction)
  <1>9. TypeOK /\ Inv16269_aa90_R0_0_I2 /\ NodeFailureAction => Inv16269_aa90_R0_0_I2' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv16269_aa90_R0_0_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv3257_59f9_R1_0_I1
THEOREM L_3 == TypeOK /\ Inv16269_aa90_R0_0_I2 /\ Inv16269_aa90_R0_0_I2 /\ Inv3257_59f9_R1_0_I1 /\ Next => Inv3257_59f9_R1_0_I1'
  <1>. USE A0
  \* (Inv3257_59f9_R1_0_I1,HRcvInvAction)
  <1>1. TypeOK /\ Inv3257_59f9_R1_0_I1 /\ HRcvInvAction => Inv3257_59f9_R1_0_I1' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv3257_59f9_R1_0_I1
  \* (Inv3257_59f9_R1_0_I1,HRcvInvNewerAction)
  <1>2. TypeOK /\ Inv3257_59f9_R1_0_I1 /\ HRcvInvNewerAction => Inv3257_59f9_R1_0_I1' BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv3257_59f9_R1_0_I1
  \* (Inv3257_59f9_R1_0_I1,HFollowerWriteReplayAction)
  <1>3. TypeOK /\ Inv16269_aa90_R0_0_I2 /\ Inv3257_59f9_R1_0_I1 /\ HFollowerWriteReplayAction => Inv3257_59f9_R1_0_I1' BY DEF TypeOK,Inv16269_aa90_R0_0_I2,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv3257_59f9_R1_0_I1
  \* (Inv3257_59f9_R1_0_I1,HRcvValAction)
  <1>4. TypeOK /\ Inv3257_59f9_R1_0_I1 /\ HRcvValAction => Inv3257_59f9_R1_0_I1' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv3257_59f9_R1_0_I1
  \* (Inv3257_59f9_R1_0_I1,HCoordWriteReplayAction)
  <1>5. TypeOK /\ Inv16269_aa90_R0_0_I2 /\ Inv3257_59f9_R1_0_I1 /\ HCoordWriteReplayAction => Inv3257_59f9_R1_0_I1' BY DEF TypeOK,Inv16269_aa90_R0_0_I2,HCoordWriteReplayAction,HCoordWriteReplay,Inv3257_59f9_R1_0_I1
  \* (Inv3257_59f9_R1_0_I1,HWriteAction)
  <1>6. TypeOK /\ Inv3257_59f9_R1_0_I1 /\ HWriteAction => Inv3257_59f9_R1_0_I1' BY DEF TypeOK,HWriteAction,HWrite,Inv3257_59f9_R1_0_I1
  \* (Inv3257_59f9_R1_0_I1,HRcvAckAction)
  <1>7. TypeOK /\ Inv3257_59f9_R1_0_I1 /\ HRcvAckAction => Inv3257_59f9_R1_0_I1' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv3257_59f9_R1_0_I1
  \* (Inv3257_59f9_R1_0_I1,HSendValsAction)
  <1>8. TypeOK /\ Inv3257_59f9_R1_0_I1 /\ HSendValsAction => Inv3257_59f9_R1_0_I1' BY DEF TypeOK,HSendValsAction,HSendVals,Inv3257_59f9_R1_0_I1,receivedAllAcks,VALMessage
  \* (Inv3257_59f9_R1_0_I1,NodeFailureAction)
  <1>9. TypeOK /\ Inv3257_59f9_R1_0_I1 /\ NodeFailureAction => Inv3257_59f9_R1_0_I1' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv3257_59f9_R1_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv2349_4d16_R0_0_I2
THEOREM L_4 == TypeOK /\ Inv2586_f463_R0_1_I2 /\ Inv2349_4d16_R0_0_I2 /\ Next => Inv2349_4d16_R0_0_I2'
  <1>. USE A0
  \* (Inv2349_4d16_R0_0_I2,HRcvInvAction)
  <1>1. TypeOK /\ Inv2349_4d16_R0_0_I2 /\ HRcvInvAction => Inv2349_4d16_R0_0_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv2349_4d16_R0_0_I2
  \* (Inv2349_4d16_R0_0_I2,HRcvInvNewerAction)
  <1>2. TypeOK /\ Inv2349_4d16_R0_0_I2 /\ HRcvInvNewerAction => Inv2349_4d16_R0_0_I2' BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv2349_4d16_R0_0_I2
  \* (Inv2349_4d16_R0_0_I2,HFollowerWriteReplayAction)
  <1>3. TypeOK /\ Inv2349_4d16_R0_0_I2 /\ HFollowerWriteReplayAction => Inv2349_4d16_R0_0_I2' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv2349_4d16_R0_0_I2
  \* (Inv2349_4d16_R0_0_I2,HRcvValAction)
  <1>4. TypeOK /\ Inv2349_4d16_R0_0_I2 /\ HRcvValAction => Inv2349_4d16_R0_0_I2' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv2349_4d16_R0_0_I2
  \* (Inv2349_4d16_R0_0_I2,HCoordWriteReplayAction)
  <1>5. TypeOK /\ Inv2349_4d16_R0_0_I2 /\ HCoordWriteReplayAction => Inv2349_4d16_R0_0_I2' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv2349_4d16_R0_0_I2
  \* (Inv2349_4d16_R0_0_I2,HWriteAction)
  <1>6. TypeOK /\ Inv2349_4d16_R0_0_I2 /\ HWriteAction => Inv2349_4d16_R0_0_I2' BY DEF TypeOK,HWriteAction,HWrite,Inv2349_4d16_R0_0_I2
  \* (Inv2349_4d16_R0_0_I2,HRcvAckAction)
  <1>7. TypeOK /\ Inv2349_4d16_R0_0_I2 /\ HRcvAckAction => Inv2349_4d16_R0_0_I2' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv2349_4d16_R0_0_I2
  \* (Inv2349_4d16_R0_0_I2,HSendValsAction)
  <1>8. TypeOK /\ Inv2586_f463_R0_1_I2 /\ Inv2349_4d16_R0_0_I2 /\ HSendValsAction => Inv2349_4d16_R0_0_I2' BY DEF TypeOK,Inv2586_f463_R0_1_I2,HSendValsAction,HSendVals,Inv2349_4d16_R0_0_I2,receivedAllAcks,VALMessage
  \* (Inv2349_4d16_R0_0_I2,NodeFailureAction)
  <1>9. TypeOK /\ Inv2349_4d16_R0_0_I2 /\ NodeFailureAction => Inv2349_4d16_R0_0_I2' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv2349_4d16_R0_0_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv2586_f463_R0_1_I2
THEOREM L_5 == TypeOK /\ Inv2796_9992_R4_0_I1 /\ Inv3739_c35e_R4_0_I1 /\ Inv2586_f463_R0_1_I2 /\ Next => Inv2586_f463_R0_1_I2'
  <1>. USE A0
  \* (Inv2586_f463_R0_1_I2,HRcvInvAction)
  <1>1. TypeOK /\ Inv2586_f463_R0_1_I2 /\ HRcvInvAction => Inv2586_f463_R0_1_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv2586_f463_R0_1_I2
  \* (Inv2586_f463_R0_1_I2,HRcvInvNewerAction)
  <1>2. TypeOK /\ Inv2586_f463_R0_1_I2 /\ HRcvInvNewerAction => Inv2586_f463_R0_1_I2' BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv2586_f463_R0_1_I2
  \* (Inv2586_f463_R0_1_I2,HFollowerWriteReplayAction)
  <1>3. TypeOK /\ Inv2586_f463_R0_1_I2 /\ HFollowerWriteReplayAction => Inv2586_f463_R0_1_I2' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv2586_f463_R0_1_I2
  \* (Inv2586_f463_R0_1_I2,HRcvValAction)
  <1>4. TypeOK /\ Inv2586_f463_R0_1_I2 /\ HRcvValAction => Inv2586_f463_R0_1_I2' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv2586_f463_R0_1_I2
  \* (Inv2586_f463_R0_1_I2,HCoordWriteReplayAction)
  <1>5. TypeOK /\ Inv2586_f463_R0_1_I2 /\ HCoordWriteReplayAction => Inv2586_f463_R0_1_I2' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv2586_f463_R0_1_I2
  \* (Inv2586_f463_R0_1_I2,HWriteAction)
  <1>6. TypeOK /\ Inv2586_f463_R0_1_I2 /\ HWriteAction => Inv2586_f463_R0_1_I2' BY DEF TypeOK,HWriteAction,HWrite,Inv2586_f463_R0_1_I2
  \* (Inv2586_f463_R0_1_I2,HRcvAckAction)
  <1>7. TypeOK /\ Inv2796_9992_R4_0_I1 /\ Inv3739_c35e_R4_0_I1 /\ Inv2586_f463_R0_1_I2 /\ HRcvAckAction => Inv2586_f463_R0_1_I2' BY DEF TypeOK,Inv2796_9992_R4_0_I1,Inv3739_c35e_R4_0_I1,HRcvAckAction,HRcvAck,Inv2586_f463_R0_1_I2
  \* (Inv2586_f463_R0_1_I2,HSendValsAction)
  <1>8. TypeOK /\ Inv2586_f463_R0_1_I2 /\ HSendValsAction => Inv2586_f463_R0_1_I2' BY DEF TypeOK,HSendValsAction,HSendVals,Inv2586_f463_R0_1_I2,receivedAllAcks,VALMessage
  \* (Inv2586_f463_R0_1_I2,NodeFailureAction)
  <1>9. TypeOK /\ Inv2586_f463_R0_1_I2 /\ NodeFailureAction => Inv2586_f463_R0_1_I2' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv2586_f463_R0_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv2796_9992_R4_0_I1
THEOREM L_6 == TypeOK /\ Inv2796_9992_R4_0_I1 /\ Next => Inv2796_9992_R4_0_I1'
  <1>. USE A0
  \* (Inv2796_9992_R4_0_I1,HRcvInvAction)
  <1>1. TypeOK /\ Inv2796_9992_R4_0_I1 /\ HRcvInvAction => Inv2796_9992_R4_0_I1' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv2796_9992_R4_0_I1
  \* (Inv2796_9992_R4_0_I1,HRcvInvNewerAction)
  <1>2. TypeOK /\ Inv2796_9992_R4_0_I1 /\ HRcvInvNewerAction => Inv2796_9992_R4_0_I1' BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv2796_9992_R4_0_I1
  \* (Inv2796_9992_R4_0_I1,HFollowerWriteReplayAction)
  <1>3. TypeOK /\ Inv2796_9992_R4_0_I1 /\ HFollowerWriteReplayAction => Inv2796_9992_R4_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv2796_9992_R4_0_I1,
                        TRUE,
                        NEW n \in aliveNodes,
                        HFollowerWriteReplay(n),
                        NEW VARI \in H_NODES'
                 PROVE  ((nodeTS[VARI] = nodeLastWriteTS[VARI]) \/ (~(nodeState[VARI] \in {"write", "replay"})))'
      BY DEF HFollowerWriteReplayAction, Inv2796_9992_R4_0_I1
    <2> QED
      BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv2796_9992_R4_0_I1
  \* (Inv2796_9992_R4_0_I1,HRcvValAction)
  <1>4. TypeOK /\ Inv2796_9992_R4_0_I1 /\ HRcvValAction => Inv2796_9992_R4_0_I1' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv2796_9992_R4_0_I1
  \* (Inv2796_9992_R4_0_I1,HCoordWriteReplayAction)
  <1>5. TypeOK /\ Inv2796_9992_R4_0_I1 /\ HCoordWriteReplayAction => Inv2796_9992_R4_0_I1' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv2796_9992_R4_0_I1
  \* (Inv2796_9992_R4_0_I1,HWriteAction)
  <1>6. TypeOK /\ Inv2796_9992_R4_0_I1 /\ HWriteAction => Inv2796_9992_R4_0_I1' BY DEF TypeOK,HWriteAction,HWrite,Inv2796_9992_R4_0_I1
  \* (Inv2796_9992_R4_0_I1,HRcvAckAction)
  <1>7. TypeOK /\ Inv2796_9992_R4_0_I1 /\ HRcvAckAction => Inv2796_9992_R4_0_I1' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv2796_9992_R4_0_I1
  \* (Inv2796_9992_R4_0_I1,HSendValsAction)
  <1>8. TypeOK /\ Inv2796_9992_R4_0_I1 /\ HSendValsAction => Inv2796_9992_R4_0_I1' BY DEF TypeOK,HSendValsAction,HSendVals,Inv2796_9992_R4_0_I1,receivedAllAcks,VALMessage
  \* (Inv2796_9992_R4_0_I1,NodeFailureAction)
  <1>9. TypeOK /\ Inv2796_9992_R4_0_I1 /\ NodeFailureAction => Inv2796_9992_R4_0_I1' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv2796_9992_R4_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv3739_c35e_R4_0_I1
THEOREM L_7 == TypeOK /\ Inv3739_c35e_R4_0_I1 /\ Next => Inv3739_c35e_R4_0_I1'
  <1>. USE A0
  \* (Inv3739_c35e_R4_0_I1,HRcvInvAction)
  <1>1. TypeOK /\ Inv3739_c35e_R4_0_I1 /\ HRcvInvAction => Inv3739_c35e_R4_0_I1' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv3739_c35e_R4_0_I1
  \* (Inv3739_c35e_R4_0_I1,HRcvInvNewerAction)
  <1>2. TypeOK /\ Inv3739_c35e_R4_0_I1 /\ HRcvInvNewerAction => Inv3739_c35e_R4_0_I1' BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv3739_c35e_R4_0_I1
  \* (Inv3739_c35e_R4_0_I1,HFollowerWriteReplayAction)
  <1>3. TypeOK /\ Inv3739_c35e_R4_0_I1 /\ HFollowerWriteReplayAction => Inv3739_c35e_R4_0_I1' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv3739_c35e_R4_0_I1
  \* (Inv3739_c35e_R4_0_I1,HRcvValAction)
  <1>4. TypeOK /\ Inv3739_c35e_R4_0_I1 /\ HRcvValAction => Inv3739_c35e_R4_0_I1' BY DEF TypeOK,HRcvValAction,HRcvVal,Inv3739_c35e_R4_0_I1
  \* (Inv3739_c35e_R4_0_I1,HCoordWriteReplayAction)
  <1>5. TypeOK /\ Inv3739_c35e_R4_0_I1 /\ HCoordWriteReplayAction => Inv3739_c35e_R4_0_I1' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv3739_c35e_R4_0_I1
  \* (Inv3739_c35e_R4_0_I1,HWriteAction)
  <1>6. TypeOK /\ Inv3739_c35e_R4_0_I1 /\ HWriteAction => Inv3739_c35e_R4_0_I1' BY DEF TypeOK,HWriteAction,HWrite,Inv3739_c35e_R4_0_I1
  \* (Inv3739_c35e_R4_0_I1,HRcvAckAction)
  <1>7. TypeOK /\ Inv3739_c35e_R4_0_I1 /\ HRcvAckAction => Inv3739_c35e_R4_0_I1' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv3739_c35e_R4_0_I1
  \* (Inv3739_c35e_R4_0_I1,HSendValsAction)
  <1>8. TypeOK /\ Inv3739_c35e_R4_0_I1 /\ HSendValsAction => Inv3739_c35e_R4_0_I1' BY DEF TypeOK,HSendValsAction,HSendVals,Inv3739_c35e_R4_0_I1,receivedAllAcks,VALMessage
  \* (Inv3739_c35e_R4_0_I1,NodeFailureAction)
  <1>9. TypeOK /\ Inv3739_c35e_R4_0_I1 /\ NodeFailureAction => Inv3739_c35e_R4_0_I1' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv3739_c35e_R4_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv2065_94b3_R0_0_I2
THEOREM L_8 == TypeOK /\ Inv2349_4d16_R0_0_I2 /\ Inv2586_f463_R0_1_I2 /\ Inv2065_94b3_R0_0_I2 /\ Next => Inv2065_94b3_R0_0_I2'
  <1>. USE A0
  \* (Inv2065_94b3_R0_0_I2,HRcvInvAction)
  <1>1. TypeOK /\ Inv2065_94b3_R0_0_I2 /\ HRcvInvAction => Inv2065_94b3_R0_0_I2' BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv2065_94b3_R0_0_I2
  \* (Inv2065_94b3_R0_0_I2,HRcvInvNewerAction)
  <1>2. TypeOK /\ Inv2065_94b3_R0_0_I2 /\ HRcvInvNewerAction => Inv2065_94b3_R0_0_I2' BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv2065_94b3_R0_0_I2
  \* (Inv2065_94b3_R0_0_I2,HFollowerWriteReplayAction)
  <1>3. TypeOK /\ Inv2065_94b3_R0_0_I2 /\ HFollowerWriteReplayAction => Inv2065_94b3_R0_0_I2' BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv2065_94b3_R0_0_I2
  \* (Inv2065_94b3_R0_0_I2,HRcvValAction)
  <1>4. TypeOK /\ Inv2349_4d16_R0_0_I2 /\ Inv2065_94b3_R0_0_I2 /\ HRcvValAction => Inv2065_94b3_R0_0_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv2349_4d16_R0_0_I2,
                        Inv2065_94b3_R0_0_I2,
                        TRUE,
                        NEW n \in aliveNodes, NEW m \in msgsVAL,
                        HRcvVal(n, m),
                        NEW VARI \in H_NODES',
                        NEW VARJ \in H_NODES'
                 PROVE  ((greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(VARI \in aliveNodes)) \/ (~(nodeState[VARJ] = "valid")))'
      BY DEF HRcvValAction, Inv2065_94b3_R0_0_I2
    <2> QED
      BY DEF TypeOK,Inv2349_4d16_R0_0_I2,HRcvValAction,HRcvVal,Inv2065_94b3_R0_0_I2
  \* (Inv2065_94b3_R0_0_I2,HCoordWriteReplayAction)
  <1>5. TypeOK /\ Inv2065_94b3_R0_0_I2 /\ HCoordWriteReplayAction => Inv2065_94b3_R0_0_I2' BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv2065_94b3_R0_0_I2
  \* (Inv2065_94b3_R0_0_I2,HWriteAction)
  <1>6. TypeOK /\ Inv2065_94b3_R0_0_I2 /\ HWriteAction => Inv2065_94b3_R0_0_I2' BY DEF TypeOK,HWriteAction,HWrite,Inv2065_94b3_R0_0_I2
  \* (Inv2065_94b3_R0_0_I2,HRcvAckAction)
  <1>7. TypeOK /\ Inv2065_94b3_R0_0_I2 /\ HRcvAckAction => Inv2065_94b3_R0_0_I2' BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv2065_94b3_R0_0_I2
  \* (Inv2065_94b3_R0_0_I2,HSendValsAction)
  <1>8. TypeOK /\ Inv2586_f463_R0_1_I2 /\ Inv2065_94b3_R0_0_I2 /\ HSendValsAction => Inv2065_94b3_R0_0_I2' BY DEF TypeOK,Inv2586_f463_R0_1_I2,HSendValsAction,HSendVals,Inv2065_94b3_R0_0_I2,receivedAllAcks,VALMessage
  \* (Inv2065_94b3_R0_0_I2,NodeFailureAction)
  <1>9. TypeOK /\ Inv2065_94b3_R0_0_I2 /\ NodeFailureAction => Inv2065_94b3_R0_0_I2' BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv2065_94b3_R0_0_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal
    <1>2. Init => Inv16269_aa90_R0_0_I2 BY DEF Init, Inv16269_aa90_R0_0_I2, IndGlobal
    <1>3. Init => Inv3257_59f9_R1_0_I1 BY DEF Init, Inv3257_59f9_R1_0_I1, IndGlobal
    <1>4. Init => Inv2349_4d16_R0_0_I2 BY DEF Init, Inv2349_4d16_R0_0_I2, IndGlobal
    <1>5. Init => Inv2586_f463_R0_1_I2 BY DEF Init, Inv2586_f463_R0_1_I2, IndGlobal
    <1>6. Init => Inv2796_9992_R4_0_I1 BY DEF Init, Inv2796_9992_R4_0_I1, IndGlobal
    <1>7. Init => Inv3739_c35e_R4_0_I1 BY DEF Init, Inv3739_c35e_R4_0_I1, IndGlobal
    <1>8. Init => Inv2065_94b3_R0_0_I2 BY DEF Init, Inv2065_94b3_R0_0_I2, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8 DEF Next, IndGlobal

=============================================================================

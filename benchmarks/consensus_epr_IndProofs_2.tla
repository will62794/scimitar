---- MODULE consensus_epr_IndProofs_2----
EXTENDS consensus_epr, FiniteSetTheorems,TLAPS

\* Proof Graph Stats
\* ==================
\* seed: 2
\* num proof graph nodes: 10
\* num proof obligations: 50
Safety == H_NoConflictingValues
Inv669_8c67_R0_0_I2 == \A VARI \in Node : \A VARJ \in Node : (decided[VARI] = {}) \/ (~(decided[VARJ] = {}) \/ (~(leader[VARJ])))
Inv1800_bd46_R1_0_I2 == \A VARI \in Node : \A VARJ \in Node : \A VARK \in Node : (NodesEq(VARI, VARK)) \/ (~(VARJ \in votes[VARK])) \/ (~(VARJ \in votes[VARI]))
Inv302_e68b_R1_0_I2 == \A VARI \in Node : \E VARQJ \in Quorum : (VARQJ = votes[VARI]) \/ ((decided[VARI] = {}))
Inv0_743a_R1_1_I2 == \A VARI \in Node : \A VARJ \in Node : (VARI = VARJ /\ leader = leader) \/ (~(leader[VARI]) \/ (~(leader[VARJ])))
Inv2322_7d97_R2_0_I2 == \A VARI \in Node : \A VARJ \in Node : \A VARK \in Node : (NodesEq(VARI, VARK)) \/ (~(<<VARJ,VARI>> \in vote_msg) \/ (~(VARJ \in votes[VARK])))
Inv3_c551_R3_0_I1 == \A VARI \in Node : \E VARQJ \in Quorum : (VARQJ = votes[VARI]) \/ (~(leader[VARI]))
Inv159_c18c_R5_0_I2 == \A VARI \in Node : \A VARJ \in Node : \A VARK \in Node : (NodesEq(VARJ, VARK)) \/ (~(<<VARI,VARJ>> \in vote_msg) \/ (~(<<VARI,VARK>> \in vote_msg)))
Inv115_c08e_R5_1_I1 == \A VARI \in Node : \A VARJ \in Node : (voted[VARJ]) \/ (~(VARJ \in votes[VARI]))
Inv6_4a42_R7_0_I1 == \A VARI \in Node : \A VARJ \in Node : (voted[VARI]) \/ (~(<<VARI,VARJ>> \in vote_msg))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv669_8c67_R0_0_I2
  /\ Inv1800_bd46_R1_0_I2
  /\ Inv2322_7d97_R2_0_I2
  /\ Inv159_c18c_R5_0_I2
  /\ Inv6_4a42_R7_0_I1
  /\ Inv115_c08e_R5_1_I1
  /\ Inv302_e68b_R1_0_I2
  /\ Inv3_c551_R3_0_I1
  /\ Inv0_743a_R1_1_I2

ASSUME QuorumsAreNodePowersets == Quorum \subseteq SUBSET Node
ASSUME EmptyNotInQuorums == {} \notin Quorum \* because quorums are majority sets
ASSUME QuorumsOverlap == \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}
ASSUME Fin == IsFiniteSet(Node) /\ IsFiniteSet(Value)
ASSUME NodeNonEmpty == Node # {}
ASSUME QuorumsNonEmpty == Quorum # {}
ASSUME NodeQuorumType == Fin /\ NodeNonEmpty /\ QuorumsAreNodePowersets /\ EmptyNotInQuorums /\ QuorumsNonEmpty

LEMMA AddingToQuorumRemainsQuorum == \A Q \in Quorum : \A s \in Node : Q \in Quorum => Q \cup {s} \in Quorum

\* If the intersection of two server sets is empty, then they can't both be quorums.
LEMMA EmptyIntersectionImpliesNotBothQuorums == 
    \A s1 \in SUBSET Node :
    \A s2 \in SUBSET Node :
        (s1 \cap s2 = {}) => ~(s1 \in Quorum /\ s2 \in Quorum)

USE Fin, FS_Subset, EmptyIntersectionImpliesNotBothQuorums, AddingToQuorumRemainsQuorum, QuorumsAreNodePowersets, EmptyNotInQuorums, QuorumsOverlap, NodeNonEmpty, QuorumsNonEmpty, NodeQuorumType DEF NodesEq

ASSUME FIVE_SERVERS_Assumption == Node = {1,2,3,4,5}

\* mean in-degree: 1.2
\* median in-degree: 1
\* max in-degree: 3
\* min in-degree: 0
\* mean variable slice size: 0


\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  \* (TypeOK,SendRequestVoteAction)
  <1>1. TypeOK /\ TypeOK /\ SendRequestVoteAction => TypeOK' BY DEF TypeOK,SendRequestVoteAction,SendRequestVote,TypeOK
  \* (TypeOK,SendVoteAction)
  <1>2. TypeOK /\ TypeOK /\ SendVoteAction => TypeOK' BY DEF TypeOK,SendVoteAction,SendVote,TypeOK
  \* (TypeOK,RecvVoteAction)
  <1>3. TypeOK /\ TypeOK /\ RecvVoteAction => TypeOK' BY DEF TypeOK,RecvVoteAction,RecvVote,TypeOK
  \* (TypeOK,BecomeLeaderAction)
  <1>4. TypeOK /\ TypeOK /\ BecomeLeaderAction => TypeOK' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,TypeOK
  \* (TypeOK,DecideAction)
  <1>5. TypeOK /\ TypeOK /\ DecideAction => TypeOK' BY DEF TypeOK,DecideAction,Decide,TypeOK
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next


\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Inv669_8c67_R0_0_I2 /\ Safety /\ Next => Safety'
  \* (Safety,SendRequestVoteAction)
  <1>1. TypeOK /\ Safety /\ SendRequestVoteAction => Safety' BY DEF TypeOK,SendRequestVoteAction,SendRequestVote,Safety,H_NoConflictingValues
  \* (Safety,SendVoteAction)
  <1>2. TypeOK /\ Safety /\ SendVoteAction => Safety' BY DEF TypeOK,SendVoteAction,SendVote,Safety,H_NoConflictingValues
  \* (Safety,RecvVoteAction)
  <1>3. TypeOK /\ Safety /\ RecvVoteAction => Safety' BY DEF TypeOK,RecvVoteAction,RecvVote,Safety,H_NoConflictingValues
  \* (Safety,BecomeLeaderAction)
  <1>4. TypeOK /\ Safety /\ BecomeLeaderAction => Safety' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Safety,H_NoConflictingValues
  \* (Safety,DecideAction)
  <1>5. TypeOK /\ Inv669_8c67_R0_0_I2 /\ Safety /\ DecideAction => Safety' BY DEF TypeOK,Inv669_8c67_R0_0_I2,DecideAction,Decide,Safety,H_NoConflictingValues
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next


\*** Inv669_8c67_R0_0_I2
THEOREM L_2 == TypeOK /\ Inv1800_bd46_R1_0_I2 /\ Inv302_e68b_R1_0_I2 /\ Inv0_743a_R1_1_I2 /\ Inv669_8c67_R0_0_I2 /\ Next => Inv669_8c67_R0_0_I2'
  \* (Inv669_8c67_R0_0_I2,SendRequestVoteAction)
  <1>1. TypeOK /\ Inv669_8c67_R0_0_I2 /\ SendRequestVoteAction => Inv669_8c67_R0_0_I2' BY DEF TypeOK,SendRequestVoteAction,SendRequestVote,Inv669_8c67_R0_0_I2
  \* (Inv669_8c67_R0_0_I2,SendVoteAction)
  <1>2. TypeOK /\ Inv669_8c67_R0_0_I2 /\ SendVoteAction => Inv669_8c67_R0_0_I2' BY DEF TypeOK,SendVoteAction,SendVote,Inv669_8c67_R0_0_I2
  \* (Inv669_8c67_R0_0_I2,RecvVoteAction)
  <1>3. TypeOK /\ Inv669_8c67_R0_0_I2 /\ RecvVoteAction => Inv669_8c67_R0_0_I2' BY DEF TypeOK,RecvVoteAction,RecvVote,Inv669_8c67_R0_0_I2
  \* (Inv669_8c67_R0_0_I2,BecomeLeaderAction)
  <1>4. TypeOK /\ Inv1800_bd46_R1_0_I2 /\ Inv302_e68b_R1_0_I2 /\ Inv669_8c67_R0_0_I2 /\ BecomeLeaderAction => Inv669_8c67_R0_0_I2' 
    <2> USE FIVE_SERVERS_Assumption
    <2> SUFFICES ASSUME TypeOK,
                        Inv1800_bd46_R1_0_I2,
                        Inv302_e68b_R1_0_I2,
                        Inv669_8c67_R0_0_I2,
                        TRUE,
                        NEW i \in Node, NEW Q \in Quorum,
                        BecomeLeader(i,Q),
                        NEW VARI \in Node',
                        NEW VARJ \in Node'
                 PROVE  ((decided[VARI] = {}) \/ (~(decided[VARJ] = {}) \/ (~(leader[VARJ]))))'
      BY DEF BecomeLeaderAction, Inv669_8c67_R0_0_I2
    <2> QED
      BY SMTT(35), FS_EmptySet, FS_Subset DEF NodesEq,TypeOK,Inv1800_bd46_R1_0_I2,Inv302_e68b_R1_0_I2,BecomeLeaderAction,BecomeLeader,Inv669_8c67_R0_0_I2
  \* (Inv669_8c67_R0_0_I2,DecideAction)
  <1>5. TypeOK /\ Inv0_743a_R1_1_I2 /\ Inv669_8c67_R0_0_I2 /\ DecideAction => Inv669_8c67_R0_0_I2' BY DEF TypeOK,Inv0_743a_R1_1_I2,DecideAction,Decide,Inv669_8c67_R0_0_I2
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next


\*** Inv1800_bd46_R1_0_I2
THEOREM L_3 == TypeOK /\ Inv2322_7d97_R2_0_I2 /\ Inv1800_bd46_R1_0_I2 /\ Next => Inv1800_bd46_R1_0_I2'
  \* (Inv1800_bd46_R1_0_I2,SendRequestVoteAction)
  <1> USE DEF NodesEq
  <1>1. TypeOK /\ Inv1800_bd46_R1_0_I2 /\ SendRequestVoteAction => Inv1800_bd46_R1_0_I2' BY DEF TypeOK,SendRequestVoteAction,SendRequestVote,Inv1800_bd46_R1_0_I2
  \* (Inv1800_bd46_R1_0_I2,SendVoteAction)
  <1>2. TypeOK /\ Inv1800_bd46_R1_0_I2 /\ SendVoteAction => Inv1800_bd46_R1_0_I2' BY DEF TypeOK,SendVoteAction,SendVote,Inv1800_bd46_R1_0_I2
  \* (Inv1800_bd46_R1_0_I2,RecvVoteAction)
  <1>3. TypeOK /\ Inv2322_7d97_R2_0_I2 /\ Inv1800_bd46_R1_0_I2 /\ RecvVoteAction => Inv1800_bd46_R1_0_I2' BY DEF TypeOK,Inv2322_7d97_R2_0_I2,RecvVoteAction,RecvVote,Inv1800_bd46_R1_0_I2
  \* (Inv1800_bd46_R1_0_I2,BecomeLeaderAction)
  <1>4. TypeOK /\ Inv1800_bd46_R1_0_I2 /\ BecomeLeaderAction => Inv1800_bd46_R1_0_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv1800_bd46_R1_0_I2
  \* (Inv1800_bd46_R1_0_I2,DecideAction)
  <1>5. TypeOK /\ Inv1800_bd46_R1_0_I2 /\ DecideAction => Inv1800_bd46_R1_0_I2' BY DEF TypeOK,DecideAction,Decide,Inv1800_bd46_R1_0_I2
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next


\*** Inv2322_7d97_R2_0_I2
THEOREM L_4 == TypeOK /\ Inv115_c08e_R5_1_I1 /\ Inv159_c18c_R5_0_I2 /\ Inv2322_7d97_R2_0_I2 /\ Next => Inv2322_7d97_R2_0_I2'
  \* (Inv2322_7d97_R2_0_I2,SendRequestVoteAction)
  <1>1. TypeOK /\ Inv2322_7d97_R2_0_I2 /\ SendRequestVoteAction => Inv2322_7d97_R2_0_I2' BY DEF TypeOK,SendRequestVoteAction,SendRequestVote,Inv2322_7d97_R2_0_I2
  \* (Inv2322_7d97_R2_0_I2,SendVoteAction)
  <1>2. TypeOK /\ Inv115_c08e_R5_1_I1 /\ Inv2322_7d97_R2_0_I2 /\ SendVoteAction => Inv2322_7d97_R2_0_I2' BY DEF TypeOK,Inv115_c08e_R5_1_I1,SendVoteAction,SendVote,Inv2322_7d97_R2_0_I2
  \* (Inv2322_7d97_R2_0_I2,RecvVoteAction)
  <1>3. TypeOK /\ Inv159_c18c_R5_0_I2 /\ Inv2322_7d97_R2_0_I2 /\ RecvVoteAction => Inv2322_7d97_R2_0_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv159_c18c_R5_0_I2,
                        Inv2322_7d97_R2_0_I2,
                        TRUE,
                        NEW i \in Node, NEW j \in Node,
                        RecvVote(i,j),
                        NEW VARI \in Node',
                        NEW VARJ \in Node',
                        NEW VARK \in Node'
                 PROVE  ((NodesEq(VARI, VARK)) \/ (~(<<VARJ,VARI>> \in vote_msg) \/ (~(VARJ \in votes[VARK]))))'
      BY DEF Inv2322_7d97_R2_0_I2, RecvVoteAction
    <2> QED
      BY DEF TypeOK,Inv159_c18c_R5_0_I2,RecvVoteAction,RecvVote,Inv2322_7d97_R2_0_I2
  \* (Inv2322_7d97_R2_0_I2,BecomeLeaderAction)
  <1>4. TypeOK /\ Inv2322_7d97_R2_0_I2 /\ BecomeLeaderAction => Inv2322_7d97_R2_0_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv2322_7d97_R2_0_I2
  \* (Inv2322_7d97_R2_0_I2,DecideAction)
  <1>5. TypeOK /\ Inv2322_7d97_R2_0_I2 /\ DecideAction => Inv2322_7d97_R2_0_I2' BY DEF TypeOK,DecideAction,Decide,Inv2322_7d97_R2_0_I2
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next


\*** Inv159_c18c_R5_0_I2
THEOREM L_5 == TypeOK /\ Inv6_4a42_R7_0_I1 /\ Inv159_c18c_R5_0_I2 /\ Next => Inv159_c18c_R5_0_I2'
  \* (Inv159_c18c_R5_0_I2,SendRequestVoteAction)
  <1>1. TypeOK /\ Inv159_c18c_R5_0_I2 /\ SendRequestVoteAction => Inv159_c18c_R5_0_I2' BY DEF TypeOK,SendRequestVoteAction,SendRequestVote,Inv159_c18c_R5_0_I2
  \* (Inv159_c18c_R5_0_I2,SendVoteAction)
  <1>2. TypeOK /\ Inv6_4a42_R7_0_I1 /\ Inv159_c18c_R5_0_I2 /\ SendVoteAction => Inv159_c18c_R5_0_I2' BY DEF TypeOK,Inv6_4a42_R7_0_I1,SendVoteAction,SendVote,Inv159_c18c_R5_0_I2
  \* (Inv159_c18c_R5_0_I2,RecvVoteAction)
  <1>3. TypeOK /\ Inv159_c18c_R5_0_I2 /\ RecvVoteAction => Inv159_c18c_R5_0_I2' BY DEF TypeOK,RecvVoteAction,RecvVote,Inv159_c18c_R5_0_I2
  \* (Inv159_c18c_R5_0_I2,BecomeLeaderAction)
  <1>4. TypeOK /\ Inv159_c18c_R5_0_I2 /\ BecomeLeaderAction => Inv159_c18c_R5_0_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv159_c18c_R5_0_I2
  \* (Inv159_c18c_R5_0_I2,DecideAction)
  <1>5. TypeOK /\ Inv159_c18c_R5_0_I2 /\ DecideAction => Inv159_c18c_R5_0_I2' BY DEF TypeOK,DecideAction,Decide,Inv159_c18c_R5_0_I2
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next


\*** Inv6_4a42_R7_0_I1
THEOREM L_6 == TypeOK /\ Inv6_4a42_R7_0_I1 /\ Next => Inv6_4a42_R7_0_I1'
  \* (Inv6_4a42_R7_0_I1,SendRequestVoteAction)
  <1>1. TypeOK /\ Inv6_4a42_R7_0_I1 /\ SendRequestVoteAction => Inv6_4a42_R7_0_I1' BY DEF TypeOK,SendRequestVoteAction,SendRequestVote,Inv6_4a42_R7_0_I1
  \* (Inv6_4a42_R7_0_I1,SendVoteAction)
  <1>2. TypeOK /\ Inv6_4a42_R7_0_I1 /\ SendVoteAction => Inv6_4a42_R7_0_I1' BY DEF TypeOK,SendVoteAction,SendVote,Inv6_4a42_R7_0_I1
  \* (Inv6_4a42_R7_0_I1,RecvVoteAction)
  <1>3. TypeOK /\ Inv6_4a42_R7_0_I1 /\ RecvVoteAction => Inv6_4a42_R7_0_I1' BY DEF TypeOK,RecvVoteAction,RecvVote,Inv6_4a42_R7_0_I1
  \* (Inv6_4a42_R7_0_I1,BecomeLeaderAction)
  <1>4. TypeOK /\ Inv6_4a42_R7_0_I1 /\ BecomeLeaderAction => Inv6_4a42_R7_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv6_4a42_R7_0_I1
  \* (Inv6_4a42_R7_0_I1,DecideAction)
  <1>5. TypeOK /\ Inv6_4a42_R7_0_I1 /\ DecideAction => Inv6_4a42_R7_0_I1' BY DEF TypeOK,DecideAction,Decide,Inv6_4a42_R7_0_I1
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next


\*** Inv115_c08e_R5_1_I1
THEOREM L_7 == TypeOK /\ Inv6_4a42_R7_0_I1 /\ Inv115_c08e_R5_1_I1 /\ Next => Inv115_c08e_R5_1_I1'
  \* (Inv115_c08e_R5_1_I1,SendRequestVoteAction)
  <1>1. TypeOK /\ Inv115_c08e_R5_1_I1 /\ SendRequestVoteAction => Inv115_c08e_R5_1_I1' BY DEF TypeOK,SendRequestVoteAction,SendRequestVote,Inv115_c08e_R5_1_I1
  \* (Inv115_c08e_R5_1_I1,SendVoteAction)
  <1>2. TypeOK /\ Inv115_c08e_R5_1_I1 /\ SendVoteAction => Inv115_c08e_R5_1_I1' BY DEF TypeOK,SendVoteAction,SendVote,Inv115_c08e_R5_1_I1
  \* (Inv115_c08e_R5_1_I1,RecvVoteAction)
  <1>3. TypeOK /\ Inv6_4a42_R7_0_I1 /\ Inv115_c08e_R5_1_I1 /\ RecvVoteAction => Inv115_c08e_R5_1_I1' BY DEF TypeOK,Inv6_4a42_R7_0_I1,RecvVoteAction,RecvVote,Inv115_c08e_R5_1_I1
  \* (Inv115_c08e_R5_1_I1,BecomeLeaderAction)
  <1>4. TypeOK /\ Inv115_c08e_R5_1_I1 /\ BecomeLeaderAction => Inv115_c08e_R5_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv115_c08e_R5_1_I1
  \* (Inv115_c08e_R5_1_I1,DecideAction)
  <1>5. TypeOK /\ Inv115_c08e_R5_1_I1 /\ DecideAction => Inv115_c08e_R5_1_I1' BY DEF TypeOK,DecideAction,Decide,Inv115_c08e_R5_1_I1
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next


\*** Inv302_e68b_R1_0_I2
THEOREM L_8 == TypeOK /\ Inv3_c551_R3_0_I1 /\ Inv302_e68b_R1_0_I2 /\ Next => Inv302_e68b_R1_0_I2'
  \* (Inv302_e68b_R1_0_I2,SendRequestVoteAction)
  <1>1. TypeOK /\ Inv302_e68b_R1_0_I2 /\ SendRequestVoteAction => Inv302_e68b_R1_0_I2' BY DEF TypeOK,SendRequestVoteAction,SendRequestVote,Inv302_e68b_R1_0_I2
  \* (Inv302_e68b_R1_0_I2,SendVoteAction)
  <1>2. TypeOK /\ Inv302_e68b_R1_0_I2 /\ SendVoteAction => Inv302_e68b_R1_0_I2' BY DEF TypeOK,SendVoteAction,SendVote,Inv302_e68b_R1_0_I2
  \* (Inv302_e68b_R1_0_I2,RecvVoteAction)
  <1>3. TypeOK /\ Inv302_e68b_R1_0_I2 /\ RecvVoteAction => Inv302_e68b_R1_0_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv302_e68b_R1_0_I2,
                        TRUE,
                        NEW i \in Node, NEW j \in Node,
                        RecvVote(i,j),
                        NEW VARI \in Node'
                 PROVE  (\E VARQJ \in Quorum : (VARQJ = votes[VARI]) \/ ((decided[VARI] = {})))'
      BY DEF Inv302_e68b_R1_0_I2, RecvVoteAction
    <2> QED
      BY DEF TypeOK,RecvVoteAction,RecvVote,Inv302_e68b_R1_0_I2
  \* (Inv302_e68b_R1_0_I2,BecomeLeaderAction)
  <1>4. TypeOK /\ Inv302_e68b_R1_0_I2 /\ BecomeLeaderAction => Inv302_e68b_R1_0_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv302_e68b_R1_0_I2
  \* (Inv302_e68b_R1_0_I2,DecideAction)
  <1>5. TypeOK /\ Inv3_c551_R3_0_I1 /\ Inv302_e68b_R1_0_I2 /\ DecideAction => Inv302_e68b_R1_0_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv3_c551_R3_0_I1,
                        Inv302_e68b_R1_0_I2,
                        TRUE,
                        NEW i \in Node, NEW j \in Node, NEW v \in Value,
                        Decide(i,v),
                        NEW VARI \in Node'
                 PROVE  (\E VARQJ \in Quorum : (VARQJ = votes[VARI]) \/ ((decided[VARI] = {})))'
      BY DEF DecideAction, Inv302_e68b_R1_0_I2
    <2> QED
      BY DEF TypeOK,Inv3_c551_R3_0_I1,DecideAction,Decide,Inv302_e68b_R1_0_I2
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next

\* Should hold for majority quorums.
LEMMA SupersetOfQuorumIsAQuorum == 
    \A S \in SUBSET Node : 
    \A Q \in Quorum : 
        (Q \subseteq S /\ (Q # S)) => 
            (S \in Quorum /\ \E QK \in Quorum : QK = S)

\*** Inv3_c551_R3_0_I1
THEOREM L_9 == TypeOK /\ Inv3_c551_R3_0_I1 /\ Next => Inv3_c551_R3_0_I1'
  \* (Inv3_c551_R3_0_I1,SendRequestVoteAction)
  <1>1. TypeOK /\ Inv3_c551_R3_0_I1 /\ SendRequestVoteAction => Inv3_c551_R3_0_I1' BY DEF TypeOK,SendRequestVoteAction,SendRequestVote,Inv3_c551_R3_0_I1
  \* (Inv3_c551_R3_0_I1,SendVoteAction)
  <1>2. TypeOK /\ Inv3_c551_R3_0_I1 /\ SendVoteAction => Inv3_c551_R3_0_I1' BY DEF TypeOK,SendVoteAction,SendVote,Inv3_c551_R3_0_I1
  \* (Inv3_c551_R3_0_I1,RecvVoteAction)
  <1>3. TypeOK /\ Inv3_c551_R3_0_I1 /\ RecvVoteAction => Inv3_c551_R3_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv3_c551_R3_0_I1,
                        TRUE,
                        NEW i \in Node, NEW j \in Node,
                        RecvVote(i,j),
                        NEW VARI \in Node'
                 PROVE  (\E VARQJ \in Quorum : (VARQJ = votes[VARI]) \/ (~(leader[VARI])))'
      BY DEF Inv3_c551_R3_0_I1, RecvVoteAction
    <2> QED
      BY FS_Subset, FS_Union DEF TypeOK,RecvVoteAction,RecvVote,Inv3_c551_R3_0_I1
  \* (Inv3_c551_R3_0_I1,BecomeLeaderAction)
  <1>4. TypeOK /\ Inv3_c551_R3_0_I1 /\ BecomeLeaderAction => Inv3_c551_R3_0_I1'
    <2> SUFFICES ASSUME TypeOK,
                        Inv3_c551_R3_0_I1,
                        TRUE,
                        NEW i \in Node, NEW Q \in Quorum,
                        BecomeLeader(i,Q),
                        NEW VARI \in Node'
                 PROVE  (\E VARQJ \in Quorum : (VARQJ = votes[VARI]) \/ (~(leader[VARI])))'
      BY DEF BecomeLeaderAction, Inv3_c551_R3_0_I1
    <2> QED
      BY SupersetOfQuorumIsAQuorum DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv3_c551_R3_0_I1
    
  \* (Inv3_c551_R3_0_I1,DecideAction)
  <1>5. TypeOK /\ Inv3_c551_R3_0_I1 /\ DecideAction => Inv3_c551_R3_0_I1' BY DEF TypeOK,DecideAction,Decide,Inv3_c551_R3_0_I1
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next


\*** Inv0_743a_R1_1_I2
THEOREM L_10 == TypeOK /\ Inv1800_bd46_R1_0_I2 /\ Inv3_c551_R3_0_I1 /\ Inv0_743a_R1_1_I2 /\ Next => Inv0_743a_R1_1_I2'
  \* (Inv0_743a_R1_1_I2,SendRequestVoteAction)
  <1>1. TypeOK /\ Inv0_743a_R1_1_I2 /\ SendRequestVoteAction => Inv0_743a_R1_1_I2' BY DEF TypeOK,SendRequestVoteAction,SendRequestVote,Inv0_743a_R1_1_I2
  \* (Inv0_743a_R1_1_I2,SendVoteAction)
  <1>2. TypeOK /\ Inv0_743a_R1_1_I2 /\ SendVoteAction => Inv0_743a_R1_1_I2' BY DEF TypeOK,SendVoteAction,SendVote,Inv0_743a_R1_1_I2
  \* (Inv0_743a_R1_1_I2,RecvVoteAction)
  <1>3. TypeOK /\ Inv0_743a_R1_1_I2 /\ RecvVoteAction => Inv0_743a_R1_1_I2' BY DEF TypeOK,RecvVoteAction,RecvVote,Inv0_743a_R1_1_I2
  \* (Inv0_743a_R1_1_I2,BecomeLeaderAction)
  <1>4. TypeOK /\ Inv1800_bd46_R1_0_I2 /\ Inv3_c551_R3_0_I1 /\ Inv0_743a_R1_1_I2 /\ BecomeLeaderAction => Inv0_743a_R1_1_I2' 
    <2> USE FIVE_SERVERS_Assumption
    <2> SUFFICES ASSUME TypeOK,
                        Inv1800_bd46_R1_0_I2,
                        Inv3_c551_R3_0_I1,
                        Inv0_743a_R1_1_I2,
                        TRUE,
                        NEW i \in Node, NEW Q \in Quorum,
                        BecomeLeader(i,Q),
                        NEW VARI \in Node',
                        NEW VARJ \in Node'
                 PROVE  ((VARI = VARJ /\ leader = leader) \/ (~(leader[VARI]) \/ (~(leader[VARJ]))))'
      BY DEF BecomeLeaderAction, Inv0_743a_R1_1_I2
    <2> QED
      BY SMTT(35) DEF TypeOK,Inv1800_bd46_R1_0_I2,Inv3_c551_R3_0_I1,BecomeLeaderAction,BecomeLeader,Inv0_743a_R1_1_I2
  \* (Inv0_743a_R1_1_I2,DecideAction)
  <1>5. TypeOK /\ Inv0_743a_R1_1_I2 /\ DecideAction => Inv0_743a_R1_1_I2' BY DEF TypeOK,DecideAction,Decide,Inv0_743a_R1_1_I2
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal, H_NoConflictingValues
    <1>2. Init => Inv669_8c67_R0_0_I2 BY DEF Init, Inv669_8c67_R0_0_I2, IndGlobal
    <1>3. Init => Inv1800_bd46_R1_0_I2 BY DEF Init, Inv1800_bd46_R1_0_I2, IndGlobal
    <1>4. Init => Inv2322_7d97_R2_0_I2 BY DEF Init, Inv2322_7d97_R2_0_I2, IndGlobal
    <1>5. Init => Inv159_c18c_R5_0_I2 BY DEF Init, Inv159_c18c_R5_0_I2, IndGlobal
    <1>6. Init => Inv6_4a42_R7_0_I1 BY DEF Init, Inv6_4a42_R7_0_I1, IndGlobal
    <1>7. Init => Inv115_c08e_R5_1_I1 BY DEF Init, Inv115_c08e_R5_1_I1, IndGlobal
    <1>8. Init => Inv302_e68b_R1_0_I2 BY DEF Init, Inv302_e68b_R1_0_I2, IndGlobal
    <1>9. Init => Inv3_c551_R3_0_I1 BY DEF Init, Inv3_c551_R3_0_I1, IndGlobal
    <1>10. Init => Inv0_743a_R1_1_I2 BY DEF Init, Inv0_743a_R1_1_I2, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10 DEF Next, IndGlobal


====

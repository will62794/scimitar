---- MODULE Bakery_IndProofs_nfm ----
EXTENDS Bakery,TLAPS, FiniteSetTheorems

\* Proof Graph Stats
\* ==================
\* seed: None
\* num proof graph nodes: 27
\* num proof obligations: 378

IndGlobal == 
  /\ TypeOK
  /\ H_MutualExclusion
  /\ H_Inv4690_2f61_R0_0_I2
  /\ H_Inv4576_59b1_R1_1_I2
  /\ H_Inv24959_7f87_R1_1_I2
  /\ H_Inv5819_32cd_R1_1_I2
  /\ H_Inv4521_3f08_R1_1_I2
  /\ H_Inv4520_48f3_R1_0_I2
  /\ H_Inv4606_2f6b_R5_0_I2
  /\ H_Inv1922_5e75_R2_0_I3
  /\ H_Inv80_b6ff_R2_0_I3
  /\ H_Inv10_8778_R2_0_I3
  /\ H_Inv5742_3d78_R2_0_I3
  /\ H_Inv32498_2818_R11_0_I2
  /\ H_Inv4227_eecc_R10_0_I3
  /\ H_Inv140_f68c_R9_0_I1
  /\ H_Inv11_3838_R8_0_I2
  /\ H_Inv61_df69_R8_0_I2
  /\ H_Inv1028_6ea5_R8_0_I2
  /\ H_Inv2740_e784_R16_0_I3
  /\ H_Inv3293_1a1e_R17_0_I3
  /\ H_Inv0_b3ba_R18_0_I0
  /\ H_Inv6093_1c74_R18_1_I2
  /\ H_Inv19_037d_R19_0_I1
  /\ H_Inv1_b58a_R20_0_I1
  /\ H_Inv350_b077_R20_1_I2
  /\ H_Inv103_c9b1_R21_1_I1
  /\ H_Inv40_180c_R24_0_I1


\* mean in-degree: 1.7407407407407407
\* median in-degree: 2
\* max in-degree: 5
\* min in-degree: 0
\* mean variable slice size: 0

ASSUME A0 == N \in Nat /\ Procs \subseteq Nat /\ IsFiniteSet(Procs)

\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  <1>. USE A0
  \* (TypeOK,ncsAction)
  <1>1. TypeOK /\ TypeOK /\ ncsAction => TypeOK' BY DEF TypeOK,ncsAction,ncs,TypeOK,\prec
  \* (TypeOK,e1aAction)
  <1>2. TypeOK /\ TypeOK /\ e1aAction => TypeOK' BY DEF TypeOK,e1aAction,e1a,TypeOK,\prec
  \* (TypeOK,e1bAction)
  <1>3. TypeOK /\ TypeOK /\ e1bAction => TypeOK' BY DEF TypeOK,e1bAction,e1b,TypeOK,\prec
  \* (TypeOK,e2aAction)
  <1>4. TypeOK /\ TypeOK /\ e2aAction => TypeOK' BY DEF TypeOK,e2aAction,e2a,TypeOK,\prec,Procs
  \* (TypeOK,e2bAction)
  <1>5. TypeOK /\ TypeOK /\ e2bAction => TypeOK' BY DEF TypeOK,e2bAction,e2b,TypeOK,\prec
  \* (TypeOK,e3aAction)
  <1>6. TypeOK /\ TypeOK /\ e3aAction => TypeOK' BY DEF TypeOK,e3aAction,e3a,TypeOK,\prec
  \* (TypeOK,e3bAction)
  <1>7. TypeOK /\ TypeOK /\ e3bAction => TypeOK' BY DEF TypeOK,e3bAction,e3b,TypeOK,\prec,\prec
  \* (TypeOK,e4aAction)
  <1>8. TypeOK /\ TypeOK /\ e4aAction => TypeOK' BY DEF TypeOK,e4aAction,e4a,TypeOK,\prec
  \* (TypeOK,e4bAction)
  <1>9. TypeOK /\ TypeOK /\ e4bAction => TypeOK' BY DEF TypeOK,e4bAction,e4b,TypeOK,\prec,\prec
  \* (TypeOK,w1aAction)
  <1>10. TypeOK /\ TypeOK /\ w1aAction => TypeOK' BY DEF TypeOK,w1aAction,w1a,TypeOK,\prec,\prec
  \* (TypeOK,w1bAction)
  <1>11. TypeOK /\ TypeOK /\ w1bAction => TypeOK' BY DEF TypeOK,w1bAction,w1b,TypeOK,\prec,\prec
  \* (TypeOK,w2Action)
  <1>12. TypeOK /\ TypeOK /\ w2Action => TypeOK' BY DEF TypeOK,w2Action,w2,TypeOK,\prec,\prec
  \* (TypeOK,csAction)
  <1>13. TypeOK /\ TypeOK /\ csAction => TypeOK' BY DEF TypeOK,csAction,cs,TypeOK,\prec
  \* (TypeOK,exitAction)
  <1>14. TypeOK /\ TypeOK /\ exitAction => TypeOK' BY DEF TypeOK,exitAction,exit,TypeOK,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv40_180c_R24_0_I1
THEOREM L_1 == TypeOK /\ H_Inv40_180c_R24_0_I1 /\ Next => H_Inv40_180c_R24_0_I1'
  <1>. USE A0
  \* (H_Inv40_180c_R24_0_I1,ncsAction)
  <1>1. TypeOK /\ H_Inv40_180c_R24_0_I1 /\ ncsAction => H_Inv40_180c_R24_0_I1' BY DEF TypeOK,ncsAction,ncs,H_Inv40_180c_R24_0_I1,\prec
  \* (H_Inv40_180c_R24_0_I1,e1aAction)
  <1>2. TypeOK /\ H_Inv40_180c_R24_0_I1 /\ e1aAction => H_Inv40_180c_R24_0_I1' BY DEF TypeOK,e1aAction,e1a,H_Inv40_180c_R24_0_I1,\prec
  \* (H_Inv40_180c_R24_0_I1,e1bAction)
  <1>3. TypeOK /\ H_Inv40_180c_R24_0_I1 /\ e1bAction => H_Inv40_180c_R24_0_I1' BY DEF TypeOK,e1bAction,e1b,H_Inv40_180c_R24_0_I1,\prec
  \* (H_Inv40_180c_R24_0_I1,e2aAction)
  <1>4. TypeOK /\ H_Inv40_180c_R24_0_I1 /\ e2aAction => H_Inv40_180c_R24_0_I1' BY DEF TypeOK,e2aAction,e2a,H_Inv40_180c_R24_0_I1,\prec,Procs
  \* (H_Inv40_180c_R24_0_I1,e2bAction)
  <1>5. TypeOK /\ H_Inv40_180c_R24_0_I1 /\ e2bAction => H_Inv40_180c_R24_0_I1' BY DEF TypeOK,e2bAction,e2b,H_Inv40_180c_R24_0_I1,\prec
  \* (H_Inv40_180c_R24_0_I1,e3aAction)
  <1>6. TypeOK /\ H_Inv40_180c_R24_0_I1 /\ e3aAction => H_Inv40_180c_R24_0_I1' BY DEF TypeOK,e3aAction,e3a,H_Inv40_180c_R24_0_I1,\prec
  \* (H_Inv40_180c_R24_0_I1,e3bAction)
  <1>7. TypeOK /\ H_Inv40_180c_R24_0_I1 /\ e3bAction => H_Inv40_180c_R24_0_I1' BY DEF TypeOK,e3bAction,e3b,H_Inv40_180c_R24_0_I1,\prec,\prec
  \* (H_Inv40_180c_R24_0_I1,e4aAction)
  <1>8. TypeOK /\ H_Inv40_180c_R24_0_I1 /\ e4aAction => H_Inv40_180c_R24_0_I1' BY DEF TypeOK,e4aAction,e4a,H_Inv40_180c_R24_0_I1,\prec
  \* (H_Inv40_180c_R24_0_I1,e4bAction)
  <1>9. TypeOK /\ H_Inv40_180c_R24_0_I1 /\ e4bAction => H_Inv40_180c_R24_0_I1' BY DEF TypeOK,e4bAction,e4b,H_Inv40_180c_R24_0_I1,\prec,\prec
  \* (H_Inv40_180c_R24_0_I1,w1aAction)
  <1>10. TypeOK /\ H_Inv40_180c_R24_0_I1 /\ w1aAction => H_Inv40_180c_R24_0_I1' BY DEF TypeOK,w1aAction,w1a,H_Inv40_180c_R24_0_I1,\prec,\prec
  \* (H_Inv40_180c_R24_0_I1,w1bAction)
  <1>11. TypeOK /\ H_Inv40_180c_R24_0_I1 /\ w1bAction => H_Inv40_180c_R24_0_I1' BY DEF TypeOK,w1bAction,w1b,H_Inv40_180c_R24_0_I1,\prec,\prec
  \* (H_Inv40_180c_R24_0_I1,w2Action)
  <1>12. TypeOK /\ H_Inv40_180c_R24_0_I1 /\ w2Action => H_Inv40_180c_R24_0_I1' BY DEF TypeOK,w2Action,w2,H_Inv40_180c_R24_0_I1,\prec,\prec
  \* (H_Inv40_180c_R24_0_I1,csAction)
  <1>13. TypeOK /\ H_Inv40_180c_R24_0_I1 /\ csAction => H_Inv40_180c_R24_0_I1' BY DEF TypeOK,csAction,cs,H_Inv40_180c_R24_0_I1,\prec
  \* (H_Inv40_180c_R24_0_I1,exitAction)
  <1>14. TypeOK /\ H_Inv40_180c_R24_0_I1 /\ exitAction => H_Inv40_180c_R24_0_I1' BY DEF TypeOK,exitAction,exit,H_Inv40_180c_R24_0_I1,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv103_c9b1_R21_1_I1
THEOREM L_2 == TypeOK /\ H_Inv40_180c_R24_0_I1 /\ H_Inv103_c9b1_R21_1_I1 /\ Next => H_Inv103_c9b1_R21_1_I1'
  <1>. USE A0
  \* (H_Inv103_c9b1_R21_1_I1,ncsAction)
  <1>1. TypeOK /\ H_Inv103_c9b1_R21_1_I1 /\ ncsAction => H_Inv103_c9b1_R21_1_I1' BY DEF TypeOK,ncsAction,ncs,H_Inv103_c9b1_R21_1_I1,\prec
  \* (H_Inv103_c9b1_R21_1_I1,e1aAction)
  <1>2. TypeOK /\ H_Inv103_c9b1_R21_1_I1 /\ e1aAction => H_Inv103_c9b1_R21_1_I1' BY DEF TypeOK,e1aAction,e1a,H_Inv103_c9b1_R21_1_I1,\prec
  \* (H_Inv103_c9b1_R21_1_I1,e1bAction)
  <1>3. TypeOK /\ H_Inv103_c9b1_R21_1_I1 /\ e1bAction => H_Inv103_c9b1_R21_1_I1' BY DEF TypeOK,e1bAction,e1b,H_Inv103_c9b1_R21_1_I1,\prec
  \* (H_Inv103_c9b1_R21_1_I1,e2aAction)
  <1>4. TypeOK /\ H_Inv103_c9b1_R21_1_I1 /\ e2aAction => H_Inv103_c9b1_R21_1_I1' BY DEF TypeOK,e2aAction,e2a,H_Inv103_c9b1_R21_1_I1,\prec,Procs
  \* (H_Inv103_c9b1_R21_1_I1,e2bAction)
  <1>5. TypeOK /\ H_Inv40_180c_R24_0_I1 /\ H_Inv103_c9b1_R21_1_I1 /\ e2bAction => H_Inv103_c9b1_R21_1_I1' BY DEF TypeOK,H_Inv40_180c_R24_0_I1,e2bAction,e2b,H_Inv103_c9b1_R21_1_I1,\prec
  \* (H_Inv103_c9b1_R21_1_I1,e3aAction)
  <1>6. TypeOK /\ H_Inv103_c9b1_R21_1_I1 /\ e3aAction => H_Inv103_c9b1_R21_1_I1' BY DEF TypeOK,e3aAction,e3a,H_Inv103_c9b1_R21_1_I1,\prec
  \* (H_Inv103_c9b1_R21_1_I1,e3bAction)
  <1>7. TypeOK /\ H_Inv103_c9b1_R21_1_I1 /\ e3bAction => H_Inv103_c9b1_R21_1_I1' BY DEF TypeOK,e3bAction,e3b,H_Inv103_c9b1_R21_1_I1,\prec,\prec
  \* (H_Inv103_c9b1_R21_1_I1,e4aAction)
  <1>8. TypeOK /\ H_Inv103_c9b1_R21_1_I1 /\ e4aAction => H_Inv103_c9b1_R21_1_I1' BY DEF TypeOK,e4aAction,e4a,H_Inv103_c9b1_R21_1_I1,\prec
  \* (H_Inv103_c9b1_R21_1_I1,e4bAction)
  <1>9. TypeOK /\ H_Inv103_c9b1_R21_1_I1 /\ e4bAction => H_Inv103_c9b1_R21_1_I1' BY DEF TypeOK,e4bAction,e4b,H_Inv103_c9b1_R21_1_I1,\prec,\prec
  \* (H_Inv103_c9b1_R21_1_I1,w1aAction)
  <1>10. TypeOK /\ H_Inv103_c9b1_R21_1_I1 /\ w1aAction => H_Inv103_c9b1_R21_1_I1' BY DEF TypeOK,w1aAction,w1a,H_Inv103_c9b1_R21_1_I1,\prec,\prec
  \* (H_Inv103_c9b1_R21_1_I1,w1bAction)
  <1>11. TypeOK /\ H_Inv103_c9b1_R21_1_I1 /\ w1bAction => H_Inv103_c9b1_R21_1_I1' BY DEF TypeOK,w1bAction,w1b,H_Inv103_c9b1_R21_1_I1,\prec,\prec
  \* (H_Inv103_c9b1_R21_1_I1,w2Action)
  <1>12. TypeOK /\ H_Inv103_c9b1_R21_1_I1 /\ w2Action => H_Inv103_c9b1_R21_1_I1' BY DEF TypeOK,w2Action,w2,H_Inv103_c9b1_R21_1_I1,\prec,\prec
  \* (H_Inv103_c9b1_R21_1_I1,csAction)
  <1>13. TypeOK /\ H_Inv103_c9b1_R21_1_I1 /\ csAction => H_Inv103_c9b1_R21_1_I1' BY DEF TypeOK,csAction,cs,H_Inv103_c9b1_R21_1_I1,\prec
  \* (H_Inv103_c9b1_R21_1_I1,exitAction)
  <1>14. TypeOK /\ H_Inv103_c9b1_R21_1_I1 /\ exitAction => H_Inv103_c9b1_R21_1_I1' BY DEF TypeOK,exitAction,exit,H_Inv103_c9b1_R21_1_I1,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv350_b077_R20_1_I2
THEOREM L_3 == TypeOK /\ H_Inv40_180c_R24_0_I1 /\ H_Inv350_b077_R20_1_I2 /\ Next => H_Inv350_b077_R20_1_I2'
  <1>. USE A0
  \* (H_Inv350_b077_R20_1_I2,ncsAction)
  <1>1. TypeOK /\ H_Inv350_b077_R20_1_I2 /\ ncsAction => H_Inv350_b077_R20_1_I2' BY DEF TypeOK,ncsAction,ncs,H_Inv350_b077_R20_1_I2,\prec
  \* (H_Inv350_b077_R20_1_I2,e1aAction)
  <1>2. TypeOK /\ H_Inv350_b077_R20_1_I2 /\ e1aAction => H_Inv350_b077_R20_1_I2' BY DEF TypeOK,e1aAction,e1a,H_Inv350_b077_R20_1_I2,\prec
  \* (H_Inv350_b077_R20_1_I2,e1bAction)
  <1>3. TypeOK /\ H_Inv350_b077_R20_1_I2 /\ e1bAction => H_Inv350_b077_R20_1_I2' BY DEF TypeOK,e1bAction,e1b,H_Inv350_b077_R20_1_I2,\prec
  \* (H_Inv350_b077_R20_1_I2,e2aAction)
  <1>4. TypeOK /\ H_Inv350_b077_R20_1_I2 /\ e2aAction => H_Inv350_b077_R20_1_I2' BY DEF TypeOK,e2aAction,e2a,H_Inv350_b077_R20_1_I2,\prec,Procs
  \* (H_Inv350_b077_R20_1_I2,e2bAction)
  <1>5. TypeOK /\ H_Inv350_b077_R20_1_I2 /\ e2bAction => H_Inv350_b077_R20_1_I2' BY DEF TypeOK,e2bAction,e2b,H_Inv350_b077_R20_1_I2,\prec
  \* (H_Inv350_b077_R20_1_I2,e3aAction)
  <1>6. TypeOK /\ H_Inv350_b077_R20_1_I2 /\ e3aAction => H_Inv350_b077_R20_1_I2' BY DEF TypeOK,e3aAction,e3a,H_Inv350_b077_R20_1_I2,\prec
  \* (H_Inv350_b077_R20_1_I2,e3bAction)
  <1>7. TypeOK /\ H_Inv350_b077_R20_1_I2 /\ e3bAction => H_Inv350_b077_R20_1_I2' BY DEF TypeOK,e3bAction,e3b,H_Inv350_b077_R20_1_I2,\prec,\prec
  \* (H_Inv350_b077_R20_1_I2,e4aAction)
  <1>8. TypeOK /\ H_Inv350_b077_R20_1_I2 /\ e4aAction => H_Inv350_b077_R20_1_I2' BY DEF TypeOK,e4aAction,e4a,H_Inv350_b077_R20_1_I2,\prec
  \* (H_Inv350_b077_R20_1_I2,e4bAction)
  <1>9. TypeOK /\ H_Inv350_b077_R20_1_I2 /\ e4bAction => H_Inv350_b077_R20_1_I2' BY DEF TypeOK,e4bAction,e4b,H_Inv350_b077_R20_1_I2,\prec,\prec
  \* (H_Inv350_b077_R20_1_I2,w1aAction)
  <1>10. TypeOK /\ H_Inv40_180c_R24_0_I1 /\ H_Inv350_b077_R20_1_I2 /\ w1aAction => H_Inv350_b077_R20_1_I2' BY DEF TypeOK,H_Inv40_180c_R24_0_I1,w1aAction,w1a,H_Inv350_b077_R20_1_I2,\prec,\prec
  \* (H_Inv350_b077_R20_1_I2,w1bAction)
  <1>11. TypeOK /\ H_Inv350_b077_R20_1_I2 /\ w1bAction => H_Inv350_b077_R20_1_I2' BY DEF TypeOK,w1bAction,w1b,H_Inv350_b077_R20_1_I2,\prec,\prec
  \* (H_Inv350_b077_R20_1_I2,w2Action)
  <1>12. TypeOK /\ H_Inv350_b077_R20_1_I2 /\ w2Action => H_Inv350_b077_R20_1_I2' BY DEF TypeOK,w2Action,w2,H_Inv350_b077_R20_1_I2,\prec,\prec
  \* (H_Inv350_b077_R20_1_I2,csAction)
  <1>13. TypeOK /\ H_Inv350_b077_R20_1_I2 /\ csAction => H_Inv350_b077_R20_1_I2' BY DEF TypeOK,csAction,cs,H_Inv350_b077_R20_1_I2,\prec
  \* (H_Inv350_b077_R20_1_I2,exitAction)
  <1>14. TypeOK /\ H_Inv350_b077_R20_1_I2 /\ exitAction => H_Inv350_b077_R20_1_I2' BY DEF TypeOK,exitAction,exit,H_Inv350_b077_R20_1_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv1_b58a_R20_0_I1
THEOREM L_4 == TypeOK /\ H_Inv350_b077_R20_1_I2 /\ H_Inv1_b58a_R20_0_I1 /\ Next => H_Inv1_b58a_R20_0_I1'
  <1>. USE A0
  \* (H_Inv1_b58a_R20_0_I1,ncsAction)
  <1>1. TypeOK /\ H_Inv1_b58a_R20_0_I1 /\ ncsAction => H_Inv1_b58a_R20_0_I1' BY DEF TypeOK,ncsAction,ncs,H_Inv1_b58a_R20_0_I1,\prec
  \* (H_Inv1_b58a_R20_0_I1,e1aAction)
  <1>2. TypeOK /\ H_Inv1_b58a_R20_0_I1 /\ e1aAction => H_Inv1_b58a_R20_0_I1' BY DEF TypeOK,e1aAction,e1a,H_Inv1_b58a_R20_0_I1,\prec
  \* (H_Inv1_b58a_R20_0_I1,e1bAction)
  <1>3. TypeOK /\ H_Inv1_b58a_R20_0_I1 /\ e1bAction => H_Inv1_b58a_R20_0_I1' BY DEF TypeOK,e1bAction,e1b,H_Inv1_b58a_R20_0_I1,\prec
  \* (H_Inv1_b58a_R20_0_I1,e2aAction)
  <1>4. TypeOK /\ H_Inv1_b58a_R20_0_I1 /\ e2aAction => H_Inv1_b58a_R20_0_I1' BY DEF TypeOK,e2aAction,e2a,H_Inv1_b58a_R20_0_I1,\prec,Procs
  \* (H_Inv1_b58a_R20_0_I1,e2bAction)
  <1>5. TypeOK /\ H_Inv1_b58a_R20_0_I1 /\ e2bAction => H_Inv1_b58a_R20_0_I1' BY DEF TypeOK,e2bAction,e2b,H_Inv1_b58a_R20_0_I1,\prec
  \* (H_Inv1_b58a_R20_0_I1,e3aAction)
  <1>6. TypeOK /\ H_Inv1_b58a_R20_0_I1 /\ e3aAction => H_Inv1_b58a_R20_0_I1' BY DEF TypeOK,e3aAction,e3a,H_Inv1_b58a_R20_0_I1,\prec
  \* (H_Inv1_b58a_R20_0_I1,e3bAction)
  <1>7. TypeOK /\ H_Inv1_b58a_R20_0_I1 /\ e3bAction => H_Inv1_b58a_R20_0_I1' BY DEF TypeOK,e3bAction,e3b,H_Inv1_b58a_R20_0_I1,\prec,\prec
  \* (H_Inv1_b58a_R20_0_I1,e4aAction)
  <1>8. TypeOK /\ H_Inv1_b58a_R20_0_I1 /\ e4aAction => H_Inv1_b58a_R20_0_I1' BY DEF TypeOK,e4aAction,e4a,H_Inv1_b58a_R20_0_I1,\prec
  \* (H_Inv1_b58a_R20_0_I1,e4bAction)
  <1>9. TypeOK /\ H_Inv1_b58a_R20_0_I1 /\ e4bAction => H_Inv1_b58a_R20_0_I1' BY DEF TypeOK,e4bAction,e4b,H_Inv1_b58a_R20_0_I1,\prec,\prec
  \* (H_Inv1_b58a_R20_0_I1,w1aAction)
  <1>10. TypeOK /\ H_Inv1_b58a_R20_0_I1 /\ w1aAction => H_Inv1_b58a_R20_0_I1' BY DEF TypeOK,w1aAction,w1a,H_Inv1_b58a_R20_0_I1,\prec,\prec
  \* (H_Inv1_b58a_R20_0_I1,w1bAction)
  <1>11. TypeOK /\ H_Inv1_b58a_R20_0_I1 /\ w1bAction => H_Inv1_b58a_R20_0_I1' BY DEF TypeOK,w1bAction,w1b,H_Inv1_b58a_R20_0_I1,\prec,\prec
  \* (H_Inv1_b58a_R20_0_I1,w2Action)
  <1>12. TypeOK /\ H_Inv350_b077_R20_1_I2 /\ H_Inv1_b58a_R20_0_I1 /\ w2Action => H_Inv1_b58a_R20_0_I1' BY DEF TypeOK,H_Inv350_b077_R20_1_I2,w2Action,w2,H_Inv1_b58a_R20_0_I1,\prec,\prec
  \* (H_Inv1_b58a_R20_0_I1,csAction)
  <1>13. TypeOK /\ H_Inv1_b58a_R20_0_I1 /\ csAction => H_Inv1_b58a_R20_0_I1' BY DEF TypeOK,csAction,cs,H_Inv1_b58a_R20_0_I1,\prec
  \* (H_Inv1_b58a_R20_0_I1,exitAction)
  <1>14. TypeOK /\ H_Inv1_b58a_R20_0_I1 /\ exitAction => H_Inv1_b58a_R20_0_I1' BY DEF TypeOK,exitAction,exit,H_Inv1_b58a_R20_0_I1,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv19_037d_R19_0_I1
THEOREM L_5 == TypeOK /\ H_Inv1_b58a_R20_0_I1 /\ H_Inv350_b077_R20_1_I2 /\ H_Inv19_037d_R19_0_I1 /\ Next => H_Inv19_037d_R19_0_I1'
  <1>. USE A0
  \* (H_Inv19_037d_R19_0_I1,ncsAction)
  <1>1. TypeOK /\ H_Inv19_037d_R19_0_I1 /\ ncsAction => H_Inv19_037d_R19_0_I1' BY DEF TypeOK,ncsAction,ncs,H_Inv19_037d_R19_0_I1,\prec
  \* (H_Inv19_037d_R19_0_I1,e1aAction)
  <1>2. TypeOK /\ H_Inv19_037d_R19_0_I1 /\ e1aAction => H_Inv19_037d_R19_0_I1' BY DEF TypeOK,e1aAction,e1a,H_Inv19_037d_R19_0_I1,\prec
  \* (H_Inv19_037d_R19_0_I1,e1bAction)
  <1>3. TypeOK /\ H_Inv19_037d_R19_0_I1 /\ e1bAction => H_Inv19_037d_R19_0_I1' BY DEF TypeOK,e1bAction,e1b,H_Inv19_037d_R19_0_I1,\prec
  \* (H_Inv19_037d_R19_0_I1,e2aAction)
  <1>4. TypeOK /\ H_Inv19_037d_R19_0_I1 /\ e2aAction => H_Inv19_037d_R19_0_I1' BY DEF TypeOK,e2aAction,e2a,H_Inv19_037d_R19_0_I1,\prec,Procs
  \* (H_Inv19_037d_R19_0_I1,e2bAction)
  <1>5. TypeOK /\ H_Inv19_037d_R19_0_I1 /\ e2bAction => H_Inv19_037d_R19_0_I1' BY DEF TypeOK,e2bAction,e2b,H_Inv19_037d_R19_0_I1,\prec
  \* (H_Inv19_037d_R19_0_I1,e3aAction)
  <1>6. TypeOK /\ H_Inv19_037d_R19_0_I1 /\ e3aAction => H_Inv19_037d_R19_0_I1' BY DEF TypeOK,e3aAction,e3a,H_Inv19_037d_R19_0_I1,\prec
  \* (H_Inv19_037d_R19_0_I1,e3bAction)
  <1>7. TypeOK /\ H_Inv19_037d_R19_0_I1 /\ e3bAction => H_Inv19_037d_R19_0_I1' BY DEF TypeOK,e3bAction,e3b,H_Inv19_037d_R19_0_I1,\prec,\prec
  \* (H_Inv19_037d_R19_0_I1,e4aAction)
  <1>8. TypeOK /\ H_Inv19_037d_R19_0_I1 /\ e4aAction => H_Inv19_037d_R19_0_I1' BY DEF TypeOK,e4aAction,e4a,H_Inv19_037d_R19_0_I1,\prec
  \* (H_Inv19_037d_R19_0_I1,e4bAction)
  <1>9. TypeOK /\ H_Inv19_037d_R19_0_I1 /\ e4bAction => H_Inv19_037d_R19_0_I1' BY DEF TypeOK,e4bAction,e4b,H_Inv19_037d_R19_0_I1,\prec,\prec
  \* (H_Inv19_037d_R19_0_I1,w1aAction)
  <1>10. TypeOK /\ H_Inv19_037d_R19_0_I1 /\ w1aAction => H_Inv19_037d_R19_0_I1' BY DEF TypeOK,w1aAction,w1a,H_Inv19_037d_R19_0_I1,\prec,\prec
  \* (H_Inv19_037d_R19_0_I1,w1bAction)
  <1>11. TypeOK /\ H_Inv19_037d_R19_0_I1 /\ w1bAction => H_Inv19_037d_R19_0_I1' BY DEF TypeOK,w1bAction,w1b,H_Inv19_037d_R19_0_I1,\prec,\prec
  \* (H_Inv19_037d_R19_0_I1,w2Action)
  <1>12. TypeOK /\ H_Inv1_b58a_R20_0_I1 /\ H_Inv350_b077_R20_1_I2 /\ H_Inv19_037d_R19_0_I1 /\ w2Action => H_Inv19_037d_R19_0_I1' BY DEF TypeOK,H_Inv1_b58a_R20_0_I1,H_Inv350_b077_R20_1_I2,w2Action,w2,H_Inv19_037d_R19_0_I1,\prec,\prec
  \* (H_Inv19_037d_R19_0_I1,csAction)
  <1>13. TypeOK /\ H_Inv19_037d_R19_0_I1 /\ csAction => H_Inv19_037d_R19_0_I1' BY DEF TypeOK,csAction,cs,H_Inv19_037d_R19_0_I1,\prec
  \* (H_Inv19_037d_R19_0_I1,exitAction)
  <1>14. TypeOK /\ H_Inv19_037d_R19_0_I1 /\ exitAction => H_Inv19_037d_R19_0_I1' BY DEF TypeOK,exitAction,exit,H_Inv19_037d_R19_0_I1,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv6093_1c74_R18_1_I2
THEOREM L_6 == TypeOK /\ H_Inv350_b077_R20_1_I2 /\ H_Inv103_c9b1_R21_1_I1 /\ H_Inv6093_1c74_R18_1_I2 /\ Next => H_Inv6093_1c74_R18_1_I2'
  <1>. USE A0
  \* (H_Inv6093_1c74_R18_1_I2,ncsAction)
  <1>1. TypeOK /\ H_Inv6093_1c74_R18_1_I2 /\ ncsAction => H_Inv6093_1c74_R18_1_I2' BY DEF TypeOK,ncsAction,ncs,H_Inv6093_1c74_R18_1_I2,\prec
  \* (H_Inv6093_1c74_R18_1_I2,e1aAction)
  <1>2. TypeOK /\ H_Inv6093_1c74_R18_1_I2 /\ e1aAction => H_Inv6093_1c74_R18_1_I2' BY DEF TypeOK,e1aAction,e1a,H_Inv6093_1c74_R18_1_I2,\prec
  \* (H_Inv6093_1c74_R18_1_I2,e1bAction)
  <1>3. TypeOK /\ H_Inv6093_1c74_R18_1_I2 /\ e1bAction => H_Inv6093_1c74_R18_1_I2' BY DEF TypeOK,e1bAction,e1b,H_Inv6093_1c74_R18_1_I2,\prec
  \* (H_Inv6093_1c74_R18_1_I2,e2aAction)
  <1>4. TypeOK /\ H_Inv6093_1c74_R18_1_I2 /\ e2aAction => H_Inv6093_1c74_R18_1_I2' BY DEF TypeOK,e2aAction,e2a,H_Inv6093_1c74_R18_1_I2,\prec,Procs
  \* (H_Inv6093_1c74_R18_1_I2,e2bAction)
  <1>5. TypeOK /\ H_Inv350_b077_R20_1_I2 /\ H_Inv6093_1c74_R18_1_I2 /\ e2bAction => H_Inv6093_1c74_R18_1_I2' BY DEF TypeOK,H_Inv350_b077_R20_1_I2,e2bAction,e2b,H_Inv6093_1c74_R18_1_I2,\prec
  \* (H_Inv6093_1c74_R18_1_I2,e3aAction)
  <1>6. TypeOK /\ H_Inv6093_1c74_R18_1_I2 /\ e3aAction => H_Inv6093_1c74_R18_1_I2' BY DEF TypeOK,e3aAction,e3a,H_Inv6093_1c74_R18_1_I2,\prec
  \* (H_Inv6093_1c74_R18_1_I2,e3bAction)
  <1>7. TypeOK /\ H_Inv6093_1c74_R18_1_I2 /\ e3bAction => H_Inv6093_1c74_R18_1_I2' BY DEF TypeOK,e3bAction,e3b,H_Inv6093_1c74_R18_1_I2,\prec,\prec
  \* (H_Inv6093_1c74_R18_1_I2,e4aAction)
  <1>8. TypeOK /\ H_Inv6093_1c74_R18_1_I2 /\ e4aAction => H_Inv6093_1c74_R18_1_I2' BY DEF TypeOK,e4aAction,e4a,H_Inv6093_1c74_R18_1_I2,\prec
  \* (H_Inv6093_1c74_R18_1_I2,e4bAction)
  <1>9. TypeOK /\ H_Inv6093_1c74_R18_1_I2 /\ e4bAction => H_Inv6093_1c74_R18_1_I2' BY DEF TypeOK,e4bAction,e4b,H_Inv6093_1c74_R18_1_I2,\prec,\prec
  \* (H_Inv6093_1c74_R18_1_I2,w1aAction)
  <1>10. TypeOK /\ H_Inv103_c9b1_R21_1_I1 /\ H_Inv6093_1c74_R18_1_I2 /\ w1aAction => H_Inv6093_1c74_R18_1_I2' BY DEF TypeOK,H_Inv103_c9b1_R21_1_I1,w1aAction,w1a,H_Inv6093_1c74_R18_1_I2,\prec,\prec
  \* (H_Inv6093_1c74_R18_1_I2,w1bAction)
  <1>11. TypeOK /\ H_Inv6093_1c74_R18_1_I2 /\ w1bAction => H_Inv6093_1c74_R18_1_I2' BY DEF TypeOK,w1bAction,w1b,H_Inv6093_1c74_R18_1_I2,\prec,\prec
  \* (H_Inv6093_1c74_R18_1_I2,w2Action)
  <1>12. TypeOK /\ H_Inv6093_1c74_R18_1_I2 /\ w2Action => H_Inv6093_1c74_R18_1_I2' BY DEF TypeOK,w2Action,w2,H_Inv6093_1c74_R18_1_I2,\prec,\prec
  \* (H_Inv6093_1c74_R18_1_I2,csAction)
  <1>13. TypeOK /\ H_Inv6093_1c74_R18_1_I2 /\ csAction => H_Inv6093_1c74_R18_1_I2' BY DEF TypeOK,csAction,cs,H_Inv6093_1c74_R18_1_I2,\prec
  \* (H_Inv6093_1c74_R18_1_I2,exitAction)
  <1>14. TypeOK /\ H_Inv6093_1c74_R18_1_I2 /\ exitAction => H_Inv6093_1c74_R18_1_I2' BY DEF TypeOK,exitAction,exit,H_Inv6093_1c74_R18_1_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv0_b3ba_R18_0_I0
THEOREM L_7 == TypeOK /\ H_Inv1_b58a_R20_0_I1 /\ H_Inv350_b077_R20_1_I2 /\ H_Inv0_b3ba_R18_0_I0 /\ Next => H_Inv0_b3ba_R18_0_I0'
  <1>. USE A0
  \* (H_Inv0_b3ba_R18_0_I0,ncsAction)
  <1>1. TypeOK /\ H_Inv0_b3ba_R18_0_I0 /\ ncsAction => H_Inv0_b3ba_R18_0_I0' BY DEF TypeOK,ncsAction,ncs,H_Inv0_b3ba_R18_0_I0,\prec
  \* (H_Inv0_b3ba_R18_0_I0,e1aAction)
  <1>2. TypeOK /\ H_Inv0_b3ba_R18_0_I0 /\ e1aAction => H_Inv0_b3ba_R18_0_I0' BY DEF TypeOK,e1aAction,e1a,H_Inv0_b3ba_R18_0_I0,\prec
  \* (H_Inv0_b3ba_R18_0_I0,e1bAction)
  <1>3. TypeOK /\ H_Inv0_b3ba_R18_0_I0 /\ e1bAction => H_Inv0_b3ba_R18_0_I0' BY DEF TypeOK,e1bAction,e1b,H_Inv0_b3ba_R18_0_I0,\prec
  \* (H_Inv0_b3ba_R18_0_I0,e2aAction)
  <1>4. TypeOK /\ H_Inv1_b58a_R20_0_I1 /\ H_Inv0_b3ba_R18_0_I0 /\ e2aAction => H_Inv0_b3ba_R18_0_I0' BY DEF TypeOK,H_Inv1_b58a_R20_0_I1,e2aAction,e2a,H_Inv0_b3ba_R18_0_I0,\prec,Procs
  \* (H_Inv0_b3ba_R18_0_I0,e2bAction)
  <1>5. TypeOK /\ H_Inv0_b3ba_R18_0_I0 /\ e2bAction => H_Inv0_b3ba_R18_0_I0' BY DEF TypeOK,e2bAction,e2b,H_Inv0_b3ba_R18_0_I0,\prec
  \* (H_Inv0_b3ba_R18_0_I0,e3aAction)
  <1>6. TypeOK /\ H_Inv0_b3ba_R18_0_I0 /\ e3aAction => H_Inv0_b3ba_R18_0_I0' BY DEF TypeOK,e3aAction,e3a,H_Inv0_b3ba_R18_0_I0,\prec
  \* (H_Inv0_b3ba_R18_0_I0,e3bAction)
  <1>7. TypeOK /\ H_Inv0_b3ba_R18_0_I0 /\ e3bAction => H_Inv0_b3ba_R18_0_I0' BY DEF TypeOK,e3bAction,e3b,H_Inv0_b3ba_R18_0_I0,\prec,\prec
  \* (H_Inv0_b3ba_R18_0_I0,e4aAction)
  <1>8. TypeOK /\ H_Inv0_b3ba_R18_0_I0 /\ e4aAction => H_Inv0_b3ba_R18_0_I0' BY DEF TypeOK,e4aAction,e4a,H_Inv0_b3ba_R18_0_I0,\prec
  \* (H_Inv0_b3ba_R18_0_I0,e4bAction)
  <1>9. TypeOK /\ H_Inv0_b3ba_R18_0_I0 /\ e4bAction => H_Inv0_b3ba_R18_0_I0' BY DEF TypeOK,e4bAction,e4b,H_Inv0_b3ba_R18_0_I0,\prec,\prec
  \* (H_Inv0_b3ba_R18_0_I0,w1aAction)
  <1>10. TypeOK /\ H_Inv0_b3ba_R18_0_I0 /\ w1aAction => H_Inv0_b3ba_R18_0_I0' BY DEF TypeOK,w1aAction,w1a,H_Inv0_b3ba_R18_0_I0,\prec,\prec
  \* (H_Inv0_b3ba_R18_0_I0,w1bAction)
  <1>11. TypeOK /\ H_Inv0_b3ba_R18_0_I0 /\ w1bAction => H_Inv0_b3ba_R18_0_I0' BY DEF TypeOK,w1bAction,w1b,H_Inv0_b3ba_R18_0_I0,\prec,\prec
  \* (H_Inv0_b3ba_R18_0_I0,w2Action)
  <1>12. TypeOK /\ H_Inv350_b077_R20_1_I2 /\ H_Inv0_b3ba_R18_0_I0 /\ w2Action => H_Inv0_b3ba_R18_0_I0' BY DEF TypeOK,H_Inv350_b077_R20_1_I2,w2Action,w2,H_Inv0_b3ba_R18_0_I0,\prec,\prec
  \* (H_Inv0_b3ba_R18_0_I0,csAction)
  <1>13. TypeOK /\ H_Inv0_b3ba_R18_0_I0 /\ csAction => H_Inv0_b3ba_R18_0_I0' BY DEF TypeOK,csAction,cs,H_Inv0_b3ba_R18_0_I0,\prec
  \* (H_Inv0_b3ba_R18_0_I0,exitAction)
  <1>14. TypeOK /\ H_Inv0_b3ba_R18_0_I0 /\ exitAction => H_Inv0_b3ba_R18_0_I0' BY DEF TypeOK,exitAction,exit,H_Inv0_b3ba_R18_0_I0,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv3293_1a1e_R17_0_I3
THEOREM L_8 == TypeOK /\ H_Inv19_037d_R19_0_I1 /\ H_Inv3293_1a1e_R17_0_I3 /\ Next => H_Inv3293_1a1e_R17_0_I3'
  <1>. USE A0
  \* (H_Inv3293_1a1e_R17_0_I3,ncsAction)
  <1>1. TypeOK /\ H_Inv3293_1a1e_R17_0_I3 /\ ncsAction => H_Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,ncsAction,ncs,H_Inv3293_1a1e_R17_0_I3,\prec
  \* (H_Inv3293_1a1e_R17_0_I3,e1aAction)
  <1>2. TypeOK /\ H_Inv3293_1a1e_R17_0_I3 /\ e1aAction => H_Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,e1aAction,e1a,H_Inv3293_1a1e_R17_0_I3,\prec
  \* (H_Inv3293_1a1e_R17_0_I3,e1bAction)
  <1>3. TypeOK /\ H_Inv3293_1a1e_R17_0_I3 /\ e1bAction => H_Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,e1bAction,e1b,H_Inv3293_1a1e_R17_0_I3,\prec
  \* (H_Inv3293_1a1e_R17_0_I3,e2aAction)
  <1>4. TypeOK /\ H_Inv3293_1a1e_R17_0_I3 /\ e2aAction => H_Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,e2aAction,e2a,H_Inv3293_1a1e_R17_0_I3,\prec,Procs
  \* (H_Inv3293_1a1e_R17_0_I3,e2bAction)
  <1>5. TypeOK /\ H_Inv3293_1a1e_R17_0_I3 /\ e2bAction => H_Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,e2bAction,e2b,H_Inv3293_1a1e_R17_0_I3,\prec
  \* (H_Inv3293_1a1e_R17_0_I3,e3aAction)
  <1>6. TypeOK /\ H_Inv3293_1a1e_R17_0_I3 /\ e3aAction => H_Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,e3aAction,e3a,H_Inv3293_1a1e_R17_0_I3,\prec
  \* (H_Inv3293_1a1e_R17_0_I3,e3bAction)
  <1>7. TypeOK /\ H_Inv3293_1a1e_R17_0_I3 /\ e3bAction => H_Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,e3bAction,e3b,H_Inv3293_1a1e_R17_0_I3,\prec,\prec
  \* (H_Inv3293_1a1e_R17_0_I3,e4aAction)
  <1>8. TypeOK /\ H_Inv3293_1a1e_R17_0_I3 /\ e4aAction => H_Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,e4aAction,e4a,H_Inv3293_1a1e_R17_0_I3,\prec
  \* (H_Inv3293_1a1e_R17_0_I3,e4bAction)
  <1>9. TypeOK /\ H_Inv3293_1a1e_R17_0_I3 /\ e4bAction => H_Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,e4bAction,e4b,H_Inv3293_1a1e_R17_0_I3,\prec,\prec
  \* (H_Inv3293_1a1e_R17_0_I3,w1aAction)
  <1>10. TypeOK /\ H_Inv3293_1a1e_R17_0_I3 /\ w1aAction => H_Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,w1aAction,w1a,H_Inv3293_1a1e_R17_0_I3,\prec,\prec
  \* (H_Inv3293_1a1e_R17_0_I3,w1bAction)
  <1>11. TypeOK /\ H_Inv19_037d_R19_0_I1 /\ H_Inv3293_1a1e_R17_0_I3 /\ w1bAction => H_Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,H_Inv19_037d_R19_0_I1,w1bAction,w1b,H_Inv3293_1a1e_R17_0_I3,\prec,\prec
  \* (H_Inv3293_1a1e_R17_0_I3,w2Action)
  <1>12. TypeOK /\ H_Inv3293_1a1e_R17_0_I3 /\ w2Action => H_Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,w2Action,w2,H_Inv3293_1a1e_R17_0_I3,\prec,\prec
  \* (H_Inv3293_1a1e_R17_0_I3,csAction)
  <1>13. TypeOK /\ H_Inv3293_1a1e_R17_0_I3 /\ csAction => H_Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,csAction,cs,H_Inv3293_1a1e_R17_0_I3,\prec
  \* (H_Inv3293_1a1e_R17_0_I3,exitAction)
  <1>14. TypeOK /\ H_Inv3293_1a1e_R17_0_I3 /\ exitAction => H_Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,exitAction,exit,H_Inv3293_1a1e_R17_0_I3,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv2740_e784_R16_0_I3
THEOREM L_9 == TypeOK /\ H_Inv0_b3ba_R18_0_I0 /\ H_Inv6093_1c74_R18_1_I2 /\ H_Inv2740_e784_R16_0_I3 /\ Next => H_Inv2740_e784_R16_0_I3'
  <1>. USE A0
  \* (H_Inv2740_e784_R16_0_I3,ncsAction)
  <1>1. TypeOK /\ H_Inv2740_e784_R16_0_I3 /\ ncsAction => H_Inv2740_e784_R16_0_I3' BY DEF TypeOK,ncsAction,ncs,H_Inv2740_e784_R16_0_I3,\prec
  \* (H_Inv2740_e784_R16_0_I3,e1aAction)
  <1>2. TypeOK /\ H_Inv2740_e784_R16_0_I3 /\ e1aAction => H_Inv2740_e784_R16_0_I3' BY DEF TypeOK,e1aAction,e1a,H_Inv2740_e784_R16_0_I3,\prec
  \* (H_Inv2740_e784_R16_0_I3,e1bAction)
  <1>3. TypeOK /\ H_Inv2740_e784_R16_0_I3 /\ e1bAction => H_Inv2740_e784_R16_0_I3' BY DEF TypeOK,e1bAction,e1b,H_Inv2740_e784_R16_0_I3,\prec
  \* (H_Inv2740_e784_R16_0_I3,e2aAction)
  <1>4. TypeOK /\ H_Inv2740_e784_R16_0_I3 /\ e2aAction => H_Inv2740_e784_R16_0_I3' BY DEF TypeOK,e2aAction,e2a,H_Inv2740_e784_R16_0_I3,\prec,Procs
  \* (H_Inv2740_e784_R16_0_I3,e2bAction)
  <1>5. TypeOK /\ H_Inv0_b3ba_R18_0_I0 /\ H_Inv2740_e784_R16_0_I3 /\ e2bAction => H_Inv2740_e784_R16_0_I3' BY DEF TypeOK,H_Inv0_b3ba_R18_0_I0,e2bAction,e2b,H_Inv2740_e784_R16_0_I3,\prec
  \* (H_Inv2740_e784_R16_0_I3,e3aAction)
  <1>6. TypeOK /\ H_Inv2740_e784_R16_0_I3 /\ e3aAction => H_Inv2740_e784_R16_0_I3' BY DEF TypeOK,e3aAction,e3a,H_Inv2740_e784_R16_0_I3,\prec
  \* (H_Inv2740_e784_R16_0_I3,e3bAction)
  <1>7. TypeOK /\ H_Inv2740_e784_R16_0_I3 /\ e3bAction => H_Inv2740_e784_R16_0_I3' BY DEF TypeOK,e3bAction,e3b,H_Inv2740_e784_R16_0_I3,\prec,\prec
  \* (H_Inv2740_e784_R16_0_I3,e4aAction)
  <1>8. TypeOK /\ H_Inv2740_e784_R16_0_I3 /\ e4aAction => H_Inv2740_e784_R16_0_I3' BY DEF TypeOK,e4aAction,e4a,H_Inv2740_e784_R16_0_I3,\prec
  \* (H_Inv2740_e784_R16_0_I3,e4bAction)
  <1>9. TypeOK /\ H_Inv2740_e784_R16_0_I3 /\ e4bAction => H_Inv2740_e784_R16_0_I3' BY DEF TypeOK,e4bAction,e4b,H_Inv2740_e784_R16_0_I3,\prec,\prec
  \* (H_Inv2740_e784_R16_0_I3,w1aAction)
  <1>10. TypeOK /\ H_Inv2740_e784_R16_0_I3 /\ w1aAction => H_Inv2740_e784_R16_0_I3' BY DEF TypeOK,w1aAction,w1a,H_Inv2740_e784_R16_0_I3,\prec,\prec
  \* (H_Inv2740_e784_R16_0_I3,w1bAction)
  <1>11. TypeOK /\ H_Inv2740_e784_R16_0_I3 /\ w1bAction => H_Inv2740_e784_R16_0_I3' BY DEF TypeOK,w1bAction,w1b,H_Inv2740_e784_R16_0_I3,\prec,\prec
  \* (H_Inv2740_e784_R16_0_I3,w2Action)
  <1>12. TypeOK /\ H_Inv6093_1c74_R18_1_I2 /\ H_Inv2740_e784_R16_0_I3 /\ w2Action => H_Inv2740_e784_R16_0_I3' BY DEF TypeOK,H_Inv6093_1c74_R18_1_I2,w2Action,w2,H_Inv2740_e784_R16_0_I3,\prec,\prec
  \* (H_Inv2740_e784_R16_0_I3,csAction)
  <1>13. TypeOK /\ H_Inv2740_e784_R16_0_I3 /\ csAction => H_Inv2740_e784_R16_0_I3' BY DEF TypeOK,csAction,cs,H_Inv2740_e784_R16_0_I3,\prec
  \* (H_Inv2740_e784_R16_0_I3,exitAction)
  <1>14. TypeOK /\ H_Inv2740_e784_R16_0_I3 /\ exitAction => H_Inv2740_e784_R16_0_I3' BY DEF TypeOK,exitAction,exit,H_Inv2740_e784_R16_0_I3,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv1028_6ea5_R8_0_I2
THEOREM L_10 == TypeOK /\ H_Inv4227_eecc_R10_0_I3 /\ H_Inv4227_eecc_R10_0_I3 /\ H_Inv80_b6ff_R2_0_I3 /\ H_Inv4227_eecc_R10_0_I3 /\ H_Inv1028_6ea5_R8_0_I2 /\ Next => H_Inv1028_6ea5_R8_0_I2'
  <1>. USE A0
  \* (H_Inv1028_6ea5_R8_0_I2,ncsAction)
  <1>1. TypeOK /\ H_Inv1028_6ea5_R8_0_I2 /\ ncsAction => H_Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,ncsAction,ncs,H_Inv1028_6ea5_R8_0_I2,\prec
  \* (H_Inv1028_6ea5_R8_0_I2,e1aAction)
  <1>2. TypeOK /\ H_Inv1028_6ea5_R8_0_I2 /\ e1aAction => H_Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,e1aAction,e1a,H_Inv1028_6ea5_R8_0_I2,\prec
  \* (H_Inv1028_6ea5_R8_0_I2,e1bAction)
  <1>3. TypeOK /\ H_Inv1028_6ea5_R8_0_I2 /\ e1bAction => H_Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,e1bAction,e1b,H_Inv1028_6ea5_R8_0_I2,\prec
  \* (H_Inv1028_6ea5_R8_0_I2,e2aAction)
  <1>4. TypeOK /\ H_Inv1028_6ea5_R8_0_I2 /\ e2aAction => H_Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,e2aAction,e2a,H_Inv1028_6ea5_R8_0_I2,\prec,Procs
  \* (H_Inv1028_6ea5_R8_0_I2,e2bAction)
  <1>5. TypeOK /\ H_Inv1028_6ea5_R8_0_I2 /\ e2bAction => H_Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,e2bAction,e2b,H_Inv1028_6ea5_R8_0_I2,\prec
  \* (H_Inv1028_6ea5_R8_0_I2,e3aAction)
  <1>6. TypeOK /\ H_Inv1028_6ea5_R8_0_I2 /\ e3aAction => H_Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,e3aAction,e3a,H_Inv1028_6ea5_R8_0_I2,\prec
  \* (H_Inv1028_6ea5_R8_0_I2,e3bAction)
  <1>7. TypeOK /\ H_Inv1028_6ea5_R8_0_I2 /\ e3bAction => H_Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,e3bAction,e3b,H_Inv1028_6ea5_R8_0_I2,\prec,\prec
  \* (H_Inv1028_6ea5_R8_0_I2,e4aAction)
  <1>8. TypeOK /\ H_Inv1028_6ea5_R8_0_I2 /\ e4aAction => H_Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,e4aAction,e4a,H_Inv1028_6ea5_R8_0_I2,\prec
  \* (H_Inv1028_6ea5_R8_0_I2,e4bAction)
  <1>9. TypeOK /\ H_Inv4227_eecc_R10_0_I3 /\ H_Inv1028_6ea5_R8_0_I2 /\ e4bAction => H_Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,H_Inv4227_eecc_R10_0_I3,e4bAction,e4b,H_Inv1028_6ea5_R8_0_I2,\prec,\prec
  \* (H_Inv1028_6ea5_R8_0_I2,w1aAction)
  <1>10. TypeOK /\ H_Inv1028_6ea5_R8_0_I2 /\ w1aAction => H_Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,w1aAction,w1a,H_Inv1028_6ea5_R8_0_I2,\prec,\prec
  \* (H_Inv1028_6ea5_R8_0_I2,w1bAction)
  <1>11. TypeOK /\ H_Inv4227_eecc_R10_0_I3 /\ H_Inv1028_6ea5_R8_0_I2 /\ w1bAction => H_Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,H_Inv4227_eecc_R10_0_I3,w1bAction,w1b,H_Inv1028_6ea5_R8_0_I2,\prec,\prec
  \* (H_Inv1028_6ea5_R8_0_I2,w2Action)
  <1>12. TypeOK /\ H_Inv80_b6ff_R2_0_I3 /\ H_Inv4227_eecc_R10_0_I3 /\ H_Inv1028_6ea5_R8_0_I2 /\ w2Action => H_Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,H_Inv80_b6ff_R2_0_I3,H_Inv4227_eecc_R10_0_I3,w2Action,w2,H_Inv1028_6ea5_R8_0_I2,\prec,\prec
  \* (H_Inv1028_6ea5_R8_0_I2,csAction)
  <1>13. TypeOK /\ H_Inv1028_6ea5_R8_0_I2 /\ csAction => H_Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,csAction,cs,H_Inv1028_6ea5_R8_0_I2,\prec
  \* (H_Inv1028_6ea5_R8_0_I2,exitAction)
  <1>14. TypeOK /\ H_Inv1028_6ea5_R8_0_I2 /\ exitAction => H_Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,exitAction,exit,H_Inv1028_6ea5_R8_0_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv61_df69_R8_0_I2
THEOREM L_11 == TypeOK /\ H_Inv61_df69_R8_0_I2 /\ Next => H_Inv61_df69_R8_0_I2'
  <1>. USE A0
  \* (H_Inv61_df69_R8_0_I2,ncsAction)
  <1>1. TypeOK /\ H_Inv61_df69_R8_0_I2 /\ ncsAction => H_Inv61_df69_R8_0_I2' BY DEF TypeOK,ncsAction,ncs,H_Inv61_df69_R8_0_I2,\prec
  \* (H_Inv61_df69_R8_0_I2,e1aAction)
  <1>2. TypeOK /\ H_Inv61_df69_R8_0_I2 /\ e1aAction => H_Inv61_df69_R8_0_I2' BY DEF TypeOK,e1aAction,e1a,H_Inv61_df69_R8_0_I2,\prec
  \* (H_Inv61_df69_R8_0_I2,e1bAction)
  <1>3. TypeOK /\ H_Inv61_df69_R8_0_I2 /\ e1bAction => H_Inv61_df69_R8_0_I2' BY DEF TypeOK,e1bAction,e1b,H_Inv61_df69_R8_0_I2,\prec
  \* (H_Inv61_df69_R8_0_I2,e2aAction)
  <1>4. TypeOK /\ H_Inv61_df69_R8_0_I2 /\ e2aAction => H_Inv61_df69_R8_0_I2' BY DEF TypeOK,e2aAction,e2a,H_Inv61_df69_R8_0_I2,\prec,Procs
  \* (H_Inv61_df69_R8_0_I2,e2bAction)
  <1>5. TypeOK /\ H_Inv61_df69_R8_0_I2 /\ e2bAction => H_Inv61_df69_R8_0_I2' BY DEF TypeOK,e2bAction,e2b,H_Inv61_df69_R8_0_I2,\prec
  \* (H_Inv61_df69_R8_0_I2,e3aAction)
  <1>6. TypeOK /\ H_Inv61_df69_R8_0_I2 /\ e3aAction => H_Inv61_df69_R8_0_I2' BY DEF TypeOK,e3aAction,e3a,H_Inv61_df69_R8_0_I2,\prec
  \* (H_Inv61_df69_R8_0_I2,e3bAction)
  <1>7. TypeOK /\ H_Inv61_df69_R8_0_I2 /\ e3bAction => H_Inv61_df69_R8_0_I2' BY DEF TypeOK,e3bAction,e3b,H_Inv61_df69_R8_0_I2,\prec,\prec
  \* (H_Inv61_df69_R8_0_I2,e4aAction)
  <1>8. TypeOK /\ H_Inv61_df69_R8_0_I2 /\ e4aAction => H_Inv61_df69_R8_0_I2' BY DEF TypeOK,e4aAction,e4a,H_Inv61_df69_R8_0_I2,\prec
  \* (H_Inv61_df69_R8_0_I2,e4bAction)
  <1>9. TypeOK /\ H_Inv61_df69_R8_0_I2 /\ e4bAction => H_Inv61_df69_R8_0_I2' BY DEF TypeOK,e4bAction,e4b,H_Inv61_df69_R8_0_I2,\prec,\prec
  \* (H_Inv61_df69_R8_0_I2,w1aAction)
  <1>10. TypeOK /\ H_Inv61_df69_R8_0_I2 /\ w1aAction => H_Inv61_df69_R8_0_I2' BY DEF TypeOK,w1aAction,w1a,H_Inv61_df69_R8_0_I2,\prec,\prec
  \* (H_Inv61_df69_R8_0_I2,w1bAction)
  <1>11. TypeOK /\ H_Inv61_df69_R8_0_I2 /\ w1bAction => H_Inv61_df69_R8_0_I2' BY DEF TypeOK,w1bAction,w1b,H_Inv61_df69_R8_0_I2,\prec,\prec
  \* (H_Inv61_df69_R8_0_I2,w2Action)
  <1>12. TypeOK /\ H_Inv61_df69_R8_0_I2 /\ w2Action => H_Inv61_df69_R8_0_I2' BY DEF TypeOK,w2Action,w2,H_Inv61_df69_R8_0_I2,\prec,\prec
  \* (H_Inv61_df69_R8_0_I2,csAction)
  <1>13. TypeOK /\ H_Inv61_df69_R8_0_I2 /\ csAction => H_Inv61_df69_R8_0_I2' BY DEF TypeOK,csAction,cs,H_Inv61_df69_R8_0_I2,\prec
  \* (H_Inv61_df69_R8_0_I2,exitAction)
  <1>14. TypeOK /\ H_Inv61_df69_R8_0_I2 /\ exitAction => H_Inv61_df69_R8_0_I2' BY DEF TypeOK,exitAction,exit,H_Inv61_df69_R8_0_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv11_3838_R8_0_I2
THEOREM L_12 == TypeOK /\ H_Inv11_3838_R8_0_I2 /\ Next => H_Inv11_3838_R8_0_I2'
  <1>. USE A0
  \* (H_Inv11_3838_R8_0_I2,ncsAction)
  <1>1. TypeOK /\ H_Inv11_3838_R8_0_I2 /\ ncsAction => H_Inv11_3838_R8_0_I2' BY DEF TypeOK,ncsAction,ncs,H_Inv11_3838_R8_0_I2,\prec
  \* (H_Inv11_3838_R8_0_I2,e1aAction)
  <1>2. TypeOK /\ H_Inv11_3838_R8_0_I2 /\ e1aAction => H_Inv11_3838_R8_0_I2' BY DEF TypeOK,e1aAction,e1a,H_Inv11_3838_R8_0_I2,\prec
  \* (H_Inv11_3838_R8_0_I2,e1bAction)
  <1>3. TypeOK /\ H_Inv11_3838_R8_0_I2 /\ e1bAction => H_Inv11_3838_R8_0_I2' BY DEF TypeOK,e1bAction,e1b,H_Inv11_3838_R8_0_I2,\prec
  \* (H_Inv11_3838_R8_0_I2,e2aAction)
  <1>4. TypeOK /\ H_Inv11_3838_R8_0_I2 /\ e2aAction => H_Inv11_3838_R8_0_I2' BY DEF TypeOK,e2aAction,e2a,H_Inv11_3838_R8_0_I2,\prec,Procs
  \* (H_Inv11_3838_R8_0_I2,e2bAction)
  <1>5. TypeOK /\ H_Inv11_3838_R8_0_I2 /\ e2bAction => H_Inv11_3838_R8_0_I2' BY DEF TypeOK,e2bAction,e2b,H_Inv11_3838_R8_0_I2,\prec
  \* (H_Inv11_3838_R8_0_I2,e3aAction)
  <1>6. TypeOK /\ H_Inv11_3838_R8_0_I2 /\ e3aAction => H_Inv11_3838_R8_0_I2' BY DEF TypeOK,e3aAction,e3a,H_Inv11_3838_R8_0_I2,\prec
  \* (H_Inv11_3838_R8_0_I2,e3bAction)
  <1>7. TypeOK /\ H_Inv11_3838_R8_0_I2 /\ e3bAction => H_Inv11_3838_R8_0_I2' BY DEF TypeOK,e3bAction,e3b,H_Inv11_3838_R8_0_I2,\prec,\prec
  \* (H_Inv11_3838_R8_0_I2,e4aAction)
  <1>8. TypeOK /\ H_Inv11_3838_R8_0_I2 /\ e4aAction => H_Inv11_3838_R8_0_I2' BY DEF TypeOK,e4aAction,e4a,H_Inv11_3838_R8_0_I2,\prec
  \* (H_Inv11_3838_R8_0_I2,e4bAction)
  <1>9. TypeOK /\ H_Inv11_3838_R8_0_I2 /\ e4bAction => H_Inv11_3838_R8_0_I2' BY DEF TypeOK,e4bAction,e4b,H_Inv11_3838_R8_0_I2,\prec,\prec
  \* (H_Inv11_3838_R8_0_I2,w1aAction)
  <1>10. TypeOK /\ H_Inv11_3838_R8_0_I2 /\ w1aAction => H_Inv11_3838_R8_0_I2' BY DEF TypeOK,w1aAction,w1a,H_Inv11_3838_R8_0_I2,\prec,\prec
  \* (H_Inv11_3838_R8_0_I2,w1bAction)
  <1>11. TypeOK /\ H_Inv11_3838_R8_0_I2 /\ w1bAction => H_Inv11_3838_R8_0_I2' BY DEF TypeOK,w1bAction,w1b,H_Inv11_3838_R8_0_I2,\prec,\prec
  \* (H_Inv11_3838_R8_0_I2,w2Action)
  <1>12. TypeOK /\ H_Inv11_3838_R8_0_I2 /\ w2Action => H_Inv11_3838_R8_0_I2' BY DEF TypeOK,w2Action,w2,H_Inv11_3838_R8_0_I2,\prec,\prec
  \* (H_Inv11_3838_R8_0_I2,csAction)
  <1>13. TypeOK /\ H_Inv11_3838_R8_0_I2 /\ csAction => H_Inv11_3838_R8_0_I2' BY DEF TypeOK,csAction,cs,H_Inv11_3838_R8_0_I2,\prec
  \* (H_Inv11_3838_R8_0_I2,exitAction)
  <1>14. TypeOK /\ H_Inv11_3838_R8_0_I2 /\ exitAction => H_Inv11_3838_R8_0_I2' BY DEF TypeOK,exitAction,exit,H_Inv11_3838_R8_0_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv140_f68c_R9_0_I1
THEOREM L_13 == TypeOK /\ H_Inv140_f68c_R9_0_I1 /\ Next => H_Inv140_f68c_R9_0_I1'
  <1>. USE A0
  \* (H_Inv140_f68c_R9_0_I1,ncsAction)
  <1>1. TypeOK /\ H_Inv140_f68c_R9_0_I1 /\ ncsAction => H_Inv140_f68c_R9_0_I1' BY DEF TypeOK,ncsAction,ncs,H_Inv140_f68c_R9_0_I1,\prec
  \* (H_Inv140_f68c_R9_0_I1,e1aAction)
  <1>2. TypeOK /\ H_Inv140_f68c_R9_0_I1 /\ e1aAction => H_Inv140_f68c_R9_0_I1' BY DEF TypeOK,e1aAction,e1a,H_Inv140_f68c_R9_0_I1,\prec
  \* (H_Inv140_f68c_R9_0_I1,e1bAction)
  <1>3. TypeOK /\ H_Inv140_f68c_R9_0_I1 /\ e1bAction => H_Inv140_f68c_R9_0_I1' BY DEF TypeOK,e1bAction,e1b,H_Inv140_f68c_R9_0_I1,\prec
  \* (H_Inv140_f68c_R9_0_I1,e2aAction)
  <1>4. TypeOK /\ H_Inv140_f68c_R9_0_I1 /\ e2aAction => H_Inv140_f68c_R9_0_I1' BY DEF TypeOK,e2aAction,e2a,H_Inv140_f68c_R9_0_I1,\prec,Procs
  \* (H_Inv140_f68c_R9_0_I1,e2bAction)
  <1>5. TypeOK /\ H_Inv140_f68c_R9_0_I1 /\ e2bAction => H_Inv140_f68c_R9_0_I1' BY DEF TypeOK,e2bAction,e2b,H_Inv140_f68c_R9_0_I1,\prec
  \* (H_Inv140_f68c_R9_0_I1,e3aAction)
  <1>6. TypeOK /\ H_Inv140_f68c_R9_0_I1 /\ e3aAction => H_Inv140_f68c_R9_0_I1' BY DEF TypeOK,e3aAction,e3a,H_Inv140_f68c_R9_0_I1,\prec
  \* (H_Inv140_f68c_R9_0_I1,e3bAction)
  <1>7. TypeOK /\ H_Inv140_f68c_R9_0_I1 /\ e3bAction => H_Inv140_f68c_R9_0_I1' BY DEF TypeOK,e3bAction,e3b,H_Inv140_f68c_R9_0_I1,\prec,\prec
  \* (H_Inv140_f68c_R9_0_I1,e4aAction)
  <1>8. TypeOK /\ H_Inv140_f68c_R9_0_I1 /\ e4aAction => H_Inv140_f68c_R9_0_I1' BY DEF TypeOK,e4aAction,e4a,H_Inv140_f68c_R9_0_I1,\prec
  \* (H_Inv140_f68c_R9_0_I1,e4bAction)
  <1>9. TypeOK /\ H_Inv140_f68c_R9_0_I1 /\ e4bAction => H_Inv140_f68c_R9_0_I1' BY DEF TypeOK,e4bAction,e4b,H_Inv140_f68c_R9_0_I1,\prec,\prec
  \* (H_Inv140_f68c_R9_0_I1,w1aAction)
  <1>10. TypeOK /\ H_Inv140_f68c_R9_0_I1 /\ w1aAction => H_Inv140_f68c_R9_0_I1' BY DEF TypeOK,w1aAction,w1a,H_Inv140_f68c_R9_0_I1,\prec,\prec
  \* (H_Inv140_f68c_R9_0_I1,w1bAction)
  <1>11. TypeOK /\ H_Inv140_f68c_R9_0_I1 /\ w1bAction => H_Inv140_f68c_R9_0_I1' BY DEF TypeOK,w1bAction,w1b,H_Inv140_f68c_R9_0_I1,\prec,\prec
  \* (H_Inv140_f68c_R9_0_I1,w2Action)
  <1>12. TypeOK /\ H_Inv140_f68c_R9_0_I1 /\ w2Action => H_Inv140_f68c_R9_0_I1' BY DEF TypeOK,w2Action,w2,H_Inv140_f68c_R9_0_I1,\prec,\prec
  \* (H_Inv140_f68c_R9_0_I1,csAction)
  <1>13. TypeOK /\ H_Inv140_f68c_R9_0_I1 /\ csAction => H_Inv140_f68c_R9_0_I1' BY DEF TypeOK,csAction,cs,H_Inv140_f68c_R9_0_I1,\prec
  \* (H_Inv140_f68c_R9_0_I1,exitAction)
  <1>14. TypeOK /\ H_Inv140_f68c_R9_0_I1 /\ exitAction => H_Inv140_f68c_R9_0_I1' BY DEF TypeOK,exitAction,exit,H_Inv140_f68c_R9_0_I1,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv4227_eecc_R10_0_I3
THEOREM L_14 == TypeOK /\ H_Inv2740_e784_R16_0_I3 /\ H_Inv140_f68c_R9_0_I1 /\ H_Inv80_b6ff_R2_0_I3 /\ H_Inv11_3838_R8_0_I2 /\ H_Inv4227_eecc_R10_0_I3 /\ Next => H_Inv4227_eecc_R10_0_I3'
  <1>. USE A0
  \* (H_Inv4227_eecc_R10_0_I3,ncsAction)
  <1>1. TypeOK /\ H_Inv4227_eecc_R10_0_I3 /\ ncsAction => H_Inv4227_eecc_R10_0_I3' BY DEF TypeOK,ncsAction,ncs,H_Inv4227_eecc_R10_0_I3,\prec
  \* (H_Inv4227_eecc_R10_0_I3,e1aAction)
  <1>2. TypeOK /\ H_Inv4227_eecc_R10_0_I3 /\ e1aAction => H_Inv4227_eecc_R10_0_I3' BY DEF TypeOK,e1aAction,e1a,H_Inv4227_eecc_R10_0_I3,\prec
  \* (H_Inv4227_eecc_R10_0_I3,e1bAction)
  <1>3. TypeOK /\ H_Inv4227_eecc_R10_0_I3 /\ e1bAction => H_Inv4227_eecc_R10_0_I3' BY DEF TypeOK,e1bAction,e1b,H_Inv4227_eecc_R10_0_I3,\prec
  \* (H_Inv4227_eecc_R10_0_I3,e2aAction)
  <1>4. TypeOK /\ H_Inv4227_eecc_R10_0_I3 /\ e2aAction => H_Inv4227_eecc_R10_0_I3' BY DEF TypeOK,e2aAction,e2a,H_Inv4227_eecc_R10_0_I3,\prec,Procs
  \* (H_Inv4227_eecc_R10_0_I3,e2bAction)
  <1>5. TypeOK /\ H_Inv4227_eecc_R10_0_I3 /\ e2bAction => H_Inv4227_eecc_R10_0_I3' BY DEF TypeOK,e2bAction,e2b,H_Inv4227_eecc_R10_0_I3,\prec
  \* (H_Inv4227_eecc_R10_0_I3,e3aAction)
  <1>6. TypeOK /\ H_Inv4227_eecc_R10_0_I3 /\ e3aAction => H_Inv4227_eecc_R10_0_I3' BY DEF TypeOK,e3aAction,e3a,H_Inv4227_eecc_R10_0_I3,\prec
  \* (H_Inv4227_eecc_R10_0_I3,e3bAction)
  <1>7. TypeOK /\ H_Inv2740_e784_R16_0_I3 /\ H_Inv4227_eecc_R10_0_I3 /\ e3bAction => H_Inv4227_eecc_R10_0_I3' BY DEF TypeOK,H_Inv2740_e784_R16_0_I3,e3bAction,e3b,H_Inv4227_eecc_R10_0_I3,\prec,\prec
  \* (H_Inv4227_eecc_R10_0_I3,e4aAction)
  <1>8. TypeOK /\ H_Inv4227_eecc_R10_0_I3 /\ e4aAction => H_Inv4227_eecc_R10_0_I3' BY DEF TypeOK,e4aAction,e4a,H_Inv4227_eecc_R10_0_I3,\prec
  \* (H_Inv4227_eecc_R10_0_I3,e4bAction)
  <1>9. TypeOK /\ H_Inv4227_eecc_R10_0_I3 /\ e4bAction => H_Inv4227_eecc_R10_0_I3' BY DEF TypeOK,e4bAction,e4b,H_Inv4227_eecc_R10_0_I3,\prec,\prec
  \* (H_Inv4227_eecc_R10_0_I3,w1aAction)
  <1>10. TypeOK /\ H_Inv4227_eecc_R10_0_I3 /\ w1aAction => H_Inv4227_eecc_R10_0_I3' BY DEF TypeOK,w1aAction,w1a,H_Inv4227_eecc_R10_0_I3,\prec,\prec
  \* (H_Inv4227_eecc_R10_0_I3,w1bAction)
  <1>11. TypeOK /\ H_Inv4227_eecc_R10_0_I3 /\ w1bAction => H_Inv4227_eecc_R10_0_I3' BY DEF TypeOK,w1bAction,w1b,H_Inv4227_eecc_R10_0_I3,\prec,\prec
  \* (H_Inv4227_eecc_R10_0_I3,w2Action)
  <1>12. TypeOK /\ H_Inv140_f68c_R9_0_I1 /\ H_Inv80_b6ff_R2_0_I3 /\ H_Inv11_3838_R8_0_I2 /\ H_Inv4227_eecc_R10_0_I3 /\ w2Action => H_Inv4227_eecc_R10_0_I3' BY DEF TypeOK,H_Inv140_f68c_R9_0_I1,H_Inv80_b6ff_R2_0_I3,H_Inv11_3838_R8_0_I2,w2Action,w2,H_Inv4227_eecc_R10_0_I3,\prec,\prec
  \* (H_Inv4227_eecc_R10_0_I3,csAction)
  <1>13. TypeOK /\ H_Inv4227_eecc_R10_0_I3 /\ csAction => H_Inv4227_eecc_R10_0_I3' BY DEF TypeOK,csAction,cs,H_Inv4227_eecc_R10_0_I3,\prec
  \* (H_Inv4227_eecc_R10_0_I3,exitAction)
  <1>14. TypeOK /\ H_Inv4227_eecc_R10_0_I3 /\ exitAction => H_Inv4227_eecc_R10_0_I3' BY DEF TypeOK,exitAction,exit,H_Inv4227_eecc_R10_0_I3,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv32498_2818_R11_0_I2
THEOREM L_15 == TypeOK /\ H_Inv3293_1a1e_R17_0_I3 /\ H_Inv2740_e784_R16_0_I3 /\ H_Inv32498_2818_R11_0_I2 /\ Next => H_Inv32498_2818_R11_0_I2'
  <1>. USE A0
  \* (H_Inv32498_2818_R11_0_I2,ncsAction)
  <1>1. TypeOK /\ H_Inv32498_2818_R11_0_I2 /\ ncsAction => H_Inv32498_2818_R11_0_I2' BY DEF TypeOK,ncsAction,ncs,H_Inv32498_2818_R11_0_I2,\prec
  \* (H_Inv32498_2818_R11_0_I2,e1aAction)
  <1>2. TypeOK /\ H_Inv32498_2818_R11_0_I2 /\ e1aAction => H_Inv32498_2818_R11_0_I2' BY DEF TypeOK,e1aAction,e1a,H_Inv32498_2818_R11_0_I2,\prec
  \* (H_Inv32498_2818_R11_0_I2,e1bAction)
  <1>3. TypeOK /\ H_Inv32498_2818_R11_0_I2 /\ e1bAction => H_Inv32498_2818_R11_0_I2' BY DEF TypeOK,e1bAction,e1b,H_Inv32498_2818_R11_0_I2,\prec
  \* (H_Inv32498_2818_R11_0_I2,e2aAction)
  <1>4. TypeOK /\ H_Inv32498_2818_R11_0_I2 /\ e2aAction => H_Inv32498_2818_R11_0_I2' BY DEF TypeOK,e2aAction,e2a,H_Inv32498_2818_R11_0_I2,\prec,Procs
  \* (H_Inv32498_2818_R11_0_I2,e2bAction)
  <1>5. TypeOK /\ H_Inv3293_1a1e_R17_0_I3 /\ H_Inv32498_2818_R11_0_I2 /\ e2bAction => H_Inv32498_2818_R11_0_I2' BY DEF TypeOK,H_Inv3293_1a1e_R17_0_I3,e2bAction,e2b,H_Inv32498_2818_R11_0_I2,\prec
  \* (H_Inv32498_2818_R11_0_I2,e3aAction)
  <1>6. TypeOK /\ H_Inv32498_2818_R11_0_I2 /\ e3aAction => H_Inv32498_2818_R11_0_I2' BY DEF TypeOK,e3aAction,e3a,H_Inv32498_2818_R11_0_I2,\prec
  \* (H_Inv32498_2818_R11_0_I2,e3bAction)
  <1>7. TypeOK /\ H_Inv32498_2818_R11_0_I2 /\ e3bAction => H_Inv32498_2818_R11_0_I2' BY DEF TypeOK,e3bAction,e3b,H_Inv32498_2818_R11_0_I2,\prec,\prec
  \* (H_Inv32498_2818_R11_0_I2,e4aAction)
  <1>8. TypeOK /\ H_Inv32498_2818_R11_0_I2 /\ e4aAction => H_Inv32498_2818_R11_0_I2' BY DEF TypeOK,e4aAction,e4a,H_Inv32498_2818_R11_0_I2,\prec
  \* (H_Inv32498_2818_R11_0_I2,e4bAction)
  <1>9. TypeOK /\ H_Inv32498_2818_R11_0_I2 /\ e4bAction => H_Inv32498_2818_R11_0_I2' BY DEF TypeOK,e4bAction,e4b,H_Inv32498_2818_R11_0_I2,\prec,\prec
  \* (H_Inv32498_2818_R11_0_I2,w1aAction)
  <1>10. TypeOK /\ H_Inv32498_2818_R11_0_I2 /\ w1aAction => H_Inv32498_2818_R11_0_I2' BY DEF TypeOK,w1aAction,w1a,H_Inv32498_2818_R11_0_I2,\prec,\prec
  \* (H_Inv32498_2818_R11_0_I2,w1bAction)
  <1>11. TypeOK /\ H_Inv2740_e784_R16_0_I3 /\ H_Inv32498_2818_R11_0_I2 /\ w1bAction => H_Inv32498_2818_R11_0_I2' BY DEF TypeOK,H_Inv2740_e784_R16_0_I3,w1bAction,w1b,H_Inv32498_2818_R11_0_I2,\prec,\prec
  \* (H_Inv32498_2818_R11_0_I2,w2Action)
  <1>12. TypeOK /\ H_Inv32498_2818_R11_0_I2 /\ w2Action => H_Inv32498_2818_R11_0_I2' BY DEF TypeOK,w2Action,w2,H_Inv32498_2818_R11_0_I2,\prec,\prec
  \* (H_Inv32498_2818_R11_0_I2,csAction)
  <1>13. TypeOK /\ H_Inv32498_2818_R11_0_I2 /\ csAction => H_Inv32498_2818_R11_0_I2' BY DEF TypeOK,csAction,cs,H_Inv32498_2818_R11_0_I2,\prec
  \* (H_Inv32498_2818_R11_0_I2,exitAction)
  <1>14. TypeOK /\ H_Inv32498_2818_R11_0_I2 /\ exitAction => H_Inv32498_2818_R11_0_I2' BY DEF TypeOK,exitAction,exit,H_Inv32498_2818_R11_0_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv5742_3d78_R2_0_I3
THEOREM L_16 == TypeOK /\ H_Inv11_3838_R8_0_I2 /\ H_Inv61_df69_R8_0_I2 /\ H_Inv1922_5e75_R2_0_I3 /\ H_Inv1028_6ea5_R8_0_I2 /\ H_Inv5742_3d78_R2_0_I3 /\ Next => H_Inv5742_3d78_R2_0_I3'
  <1>. USE A0
  \* (H_Inv5742_3d78_R2_0_I3,ncsAction)
  <1>1. TypeOK /\ H_Inv5742_3d78_R2_0_I3 /\ ncsAction => H_Inv5742_3d78_R2_0_I3' BY DEF TypeOK,ncsAction,ncs,H_Inv5742_3d78_R2_0_I3,\prec
  \* (H_Inv5742_3d78_R2_0_I3,e1aAction)
  <1>2. TypeOK /\ H_Inv5742_3d78_R2_0_I3 /\ e1aAction => H_Inv5742_3d78_R2_0_I3' BY DEF TypeOK,e1aAction,e1a,H_Inv5742_3d78_R2_0_I3,\prec
  \* (H_Inv5742_3d78_R2_0_I3,e1bAction)
  <1>3. TypeOK /\ H_Inv5742_3d78_R2_0_I3 /\ e1bAction => H_Inv5742_3d78_R2_0_I3' BY DEF TypeOK,e1bAction,e1b,H_Inv5742_3d78_R2_0_I3,\prec
  \* (H_Inv5742_3d78_R2_0_I3,e2aAction)
  <1>4. TypeOK /\ H_Inv5742_3d78_R2_0_I3 /\ e2aAction => H_Inv5742_3d78_R2_0_I3' BY DEF TypeOK,e2aAction,e2a,H_Inv5742_3d78_R2_0_I3,\prec,Procs
  \* (H_Inv5742_3d78_R2_0_I3,e2bAction)
  <1>5. TypeOK /\ H_Inv5742_3d78_R2_0_I3 /\ e2bAction => H_Inv5742_3d78_R2_0_I3' BY DEF TypeOK,e2bAction,e2b,H_Inv5742_3d78_R2_0_I3,\prec
  \* (H_Inv5742_3d78_R2_0_I3,e3aAction)
  <1>6. TypeOK /\ H_Inv5742_3d78_R2_0_I3 /\ e3aAction => H_Inv5742_3d78_R2_0_I3' BY DEF TypeOK,e3aAction,e3a,H_Inv5742_3d78_R2_0_I3,\prec
  \* (H_Inv5742_3d78_R2_0_I3,e3bAction)
  <1>7. TypeOK /\ H_Inv5742_3d78_R2_0_I3 /\ e3bAction => H_Inv5742_3d78_R2_0_I3' BY DEF TypeOK,e3bAction,e3b,H_Inv5742_3d78_R2_0_I3,\prec,\prec
  \* (H_Inv5742_3d78_R2_0_I3,e4aAction)
  <1>8. TypeOK /\ H_Inv5742_3d78_R2_0_I3 /\ e4aAction => H_Inv5742_3d78_R2_0_I3' BY DEF TypeOK,e4aAction,e4a,H_Inv5742_3d78_R2_0_I3,\prec
  \* (H_Inv5742_3d78_R2_0_I3,e4bAction)
  <1>9. TypeOK /\ H_Inv5742_3d78_R2_0_I3 /\ e4bAction => H_Inv5742_3d78_R2_0_I3' BY DEF TypeOK,e4bAction,e4b,H_Inv5742_3d78_R2_0_I3,\prec,\prec
  \* (H_Inv5742_3d78_R2_0_I3,w1aAction)
  <1>10. TypeOK /\ H_Inv11_3838_R8_0_I2 /\ H_Inv61_df69_R8_0_I2 /\ H_Inv1922_5e75_R2_0_I3 /\ H_Inv1028_6ea5_R8_0_I2 /\ H_Inv5742_3d78_R2_0_I3 /\ w1aAction => H_Inv5742_3d78_R2_0_I3' BY DEF TypeOK,H_Inv11_3838_R8_0_I2,H_Inv61_df69_R8_0_I2,H_Inv1922_5e75_R2_0_I3,H_Inv1028_6ea5_R8_0_I2,w1aAction,w1a,H_Inv5742_3d78_R2_0_I3,\prec,\prec
  \* (H_Inv5742_3d78_R2_0_I3,w1bAction)
  <1>11. TypeOK /\ H_Inv5742_3d78_R2_0_I3 /\ w1bAction => H_Inv5742_3d78_R2_0_I3' BY DEF TypeOK,w1bAction,w1b,H_Inv5742_3d78_R2_0_I3,\prec,\prec
  \* (H_Inv5742_3d78_R2_0_I3,w2Action)
  <1>12. TypeOK /\ H_Inv5742_3d78_R2_0_I3 /\ w2Action => H_Inv5742_3d78_R2_0_I3' BY DEF TypeOK,w2Action,w2,H_Inv5742_3d78_R2_0_I3,\prec,\prec
  \* (H_Inv5742_3d78_R2_0_I3,csAction)
  <1>13. TypeOK /\ H_Inv5742_3d78_R2_0_I3 /\ csAction => H_Inv5742_3d78_R2_0_I3' BY DEF TypeOK,csAction,cs,H_Inv5742_3d78_R2_0_I3,\prec
  \* (H_Inv5742_3d78_R2_0_I3,exitAction)
  <1>14. TypeOK /\ H_Inv5742_3d78_R2_0_I3 /\ exitAction => H_Inv5742_3d78_R2_0_I3' BY DEF TypeOK,exitAction,exit,H_Inv5742_3d78_R2_0_I3,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv10_8778_R2_0_I3
THEOREM L_17 == TypeOK /\ H_Inv10_8778_R2_0_I3 /\ Next => H_Inv10_8778_R2_0_I3'
  <1>. USE A0
  \* (H_Inv10_8778_R2_0_I3,ncsAction)
  <1>1. TypeOK /\ H_Inv10_8778_R2_0_I3 /\ ncsAction => H_Inv10_8778_R2_0_I3' BY DEF TypeOK,ncsAction,ncs,H_Inv10_8778_R2_0_I3,\prec
  \* (H_Inv10_8778_R2_0_I3,e1aAction)
  <1>2. TypeOK /\ H_Inv10_8778_R2_0_I3 /\ e1aAction => H_Inv10_8778_R2_0_I3' BY DEF TypeOK,e1aAction,e1a,H_Inv10_8778_R2_0_I3,\prec
  \* (H_Inv10_8778_R2_0_I3,e1bAction)
  <1>3. TypeOK /\ H_Inv10_8778_R2_0_I3 /\ e1bAction => H_Inv10_8778_R2_0_I3' BY DEF TypeOK,e1bAction,e1b,H_Inv10_8778_R2_0_I3,\prec
  \* (H_Inv10_8778_R2_0_I3,e2aAction)
  <1>4. TypeOK /\ H_Inv10_8778_R2_0_I3 /\ e2aAction => H_Inv10_8778_R2_0_I3' BY DEF TypeOK,e2aAction,e2a,H_Inv10_8778_R2_0_I3,\prec,Procs
  \* (H_Inv10_8778_R2_0_I3,e2bAction)
  <1>5. TypeOK /\ H_Inv10_8778_R2_0_I3 /\ e2bAction => H_Inv10_8778_R2_0_I3' BY DEF TypeOK,e2bAction,e2b,H_Inv10_8778_R2_0_I3,\prec
  \* (H_Inv10_8778_R2_0_I3,e3aAction)
  <1>6. TypeOK /\ H_Inv10_8778_R2_0_I3 /\ e3aAction => H_Inv10_8778_R2_0_I3' BY DEF TypeOK,e3aAction,e3a,H_Inv10_8778_R2_0_I3,\prec
  \* (H_Inv10_8778_R2_0_I3,e3bAction)
  <1>7. TypeOK /\ H_Inv10_8778_R2_0_I3 /\ e3bAction => H_Inv10_8778_R2_0_I3' BY DEF TypeOK,e3bAction,e3b,H_Inv10_8778_R2_0_I3,\prec,\prec
  \* (H_Inv10_8778_R2_0_I3,e4aAction)
  <1>8. TypeOK /\ H_Inv10_8778_R2_0_I3 /\ e4aAction => H_Inv10_8778_R2_0_I3' BY DEF TypeOK,e4aAction,e4a,H_Inv10_8778_R2_0_I3,\prec
  \* (H_Inv10_8778_R2_0_I3,e4bAction)
  <1>9. TypeOK /\ H_Inv10_8778_R2_0_I3 /\ e4bAction => H_Inv10_8778_R2_0_I3' BY DEF TypeOK,e4bAction,e4b,H_Inv10_8778_R2_0_I3,\prec,\prec
  \* (H_Inv10_8778_R2_0_I3,w1aAction)
  <1>10. TypeOK /\ H_Inv10_8778_R2_0_I3 /\ w1aAction => H_Inv10_8778_R2_0_I3' BY DEF TypeOK,w1aAction,w1a,H_Inv10_8778_R2_0_I3,\prec,\prec
  \* (H_Inv10_8778_R2_0_I3,w1bAction)
  <1>11. TypeOK /\ H_Inv10_8778_R2_0_I3 /\ w1bAction => H_Inv10_8778_R2_0_I3' BY DEF TypeOK,w1bAction,w1b,H_Inv10_8778_R2_0_I3,\prec,\prec
  \* (H_Inv10_8778_R2_0_I3,w2Action)
  <1>12. TypeOK /\ H_Inv10_8778_R2_0_I3 /\ w2Action => H_Inv10_8778_R2_0_I3' BY DEF TypeOK,w2Action,w2,H_Inv10_8778_R2_0_I3,\prec,\prec
  \* (H_Inv10_8778_R2_0_I3,csAction)
  <1>13. TypeOK /\ H_Inv10_8778_R2_0_I3 /\ csAction => H_Inv10_8778_R2_0_I3' BY DEF TypeOK,csAction,cs,H_Inv10_8778_R2_0_I3,\prec
  \* (H_Inv10_8778_R2_0_I3,exitAction)
  <1>14. TypeOK /\ H_Inv10_8778_R2_0_I3 /\ exitAction => H_Inv10_8778_R2_0_I3' BY DEF TypeOK,exitAction,exit,H_Inv10_8778_R2_0_I3,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv80_b6ff_R2_0_I3
THEOREM L_18 == TypeOK /\ H_Inv140_f68c_R9_0_I1 /\ H_Inv80_b6ff_R2_0_I3 /\ Next => H_Inv80_b6ff_R2_0_I3'
  <1>. USE A0
  \* (H_Inv80_b6ff_R2_0_I3,ncsAction)
  <1>1. TypeOK /\ H_Inv80_b6ff_R2_0_I3 /\ ncsAction => H_Inv80_b6ff_R2_0_I3' BY DEF TypeOK,ncsAction,ncs,H_Inv80_b6ff_R2_0_I3,\prec
  \* (H_Inv80_b6ff_R2_0_I3,e1aAction)
  <1>2. TypeOK /\ H_Inv80_b6ff_R2_0_I3 /\ e1aAction => H_Inv80_b6ff_R2_0_I3' BY DEF TypeOK,e1aAction,e1a,H_Inv80_b6ff_R2_0_I3,\prec
  \* (H_Inv80_b6ff_R2_0_I3,e1bAction)
  <1>3. TypeOK /\ H_Inv80_b6ff_R2_0_I3 /\ e1bAction => H_Inv80_b6ff_R2_0_I3' BY DEF TypeOK,e1bAction,e1b,H_Inv80_b6ff_R2_0_I3,\prec
  \* (H_Inv80_b6ff_R2_0_I3,e2aAction)
  <1>4. TypeOK /\ H_Inv80_b6ff_R2_0_I3 /\ e2aAction => H_Inv80_b6ff_R2_0_I3' BY DEF TypeOK,e2aAction,e2a,H_Inv80_b6ff_R2_0_I3,\prec,Procs
  \* (H_Inv80_b6ff_R2_0_I3,e2bAction)
  <1>5. TypeOK /\ H_Inv80_b6ff_R2_0_I3 /\ e2bAction => H_Inv80_b6ff_R2_0_I3' BY DEF TypeOK,e2bAction,e2b,H_Inv80_b6ff_R2_0_I3,\prec
  \* (H_Inv80_b6ff_R2_0_I3,e3aAction)
  <1>6. TypeOK /\ H_Inv80_b6ff_R2_0_I3 /\ e3aAction => H_Inv80_b6ff_R2_0_I3' BY DEF TypeOK,e3aAction,e3a,H_Inv80_b6ff_R2_0_I3,\prec
  \* (H_Inv80_b6ff_R2_0_I3,e3bAction)
  <1>7. TypeOK /\ H_Inv80_b6ff_R2_0_I3 /\ e3bAction => H_Inv80_b6ff_R2_0_I3' BY DEF TypeOK,e3bAction,e3b,H_Inv80_b6ff_R2_0_I3,\prec,\prec
  \* (H_Inv80_b6ff_R2_0_I3,e4aAction)
  <1>8. TypeOK /\ H_Inv80_b6ff_R2_0_I3 /\ e4aAction => H_Inv80_b6ff_R2_0_I3' BY DEF TypeOK,e4aAction,e4a,H_Inv80_b6ff_R2_0_I3,\prec
  \* (H_Inv80_b6ff_R2_0_I3,e4bAction)
  <1>9. TypeOK /\ H_Inv140_f68c_R9_0_I1 /\ H_Inv80_b6ff_R2_0_I3 /\ e4bAction => H_Inv80_b6ff_R2_0_I3' BY DEF TypeOK,H_Inv140_f68c_R9_0_I1,e4bAction,e4b,H_Inv80_b6ff_R2_0_I3,\prec,\prec
  \* (H_Inv80_b6ff_R2_0_I3,w1aAction)
  <1>10. TypeOK /\ H_Inv80_b6ff_R2_0_I3 /\ w1aAction => H_Inv80_b6ff_R2_0_I3' BY DEF TypeOK,w1aAction,w1a,H_Inv80_b6ff_R2_0_I3,\prec,\prec
  \* (H_Inv80_b6ff_R2_0_I3,w1bAction)
  <1>11. TypeOK /\ H_Inv80_b6ff_R2_0_I3 /\ w1bAction => H_Inv80_b6ff_R2_0_I3' BY DEF TypeOK,w1bAction,w1b,H_Inv80_b6ff_R2_0_I3,\prec,\prec
  \* (H_Inv80_b6ff_R2_0_I3,w2Action)
  <1>12. TypeOK /\ H_Inv80_b6ff_R2_0_I3 /\ w2Action => H_Inv80_b6ff_R2_0_I3' BY DEF TypeOK,w2Action,w2,H_Inv80_b6ff_R2_0_I3,\prec,\prec
  \* (H_Inv80_b6ff_R2_0_I3,csAction)
  <1>13. TypeOK /\ H_Inv80_b6ff_R2_0_I3 /\ csAction => H_Inv80_b6ff_R2_0_I3' BY DEF TypeOK,csAction,cs,H_Inv80_b6ff_R2_0_I3,\prec
  \* (H_Inv80_b6ff_R2_0_I3,exitAction)
  <1>14. TypeOK /\ H_Inv80_b6ff_R2_0_I3 /\ exitAction => H_Inv80_b6ff_R2_0_I3' BY DEF TypeOK,exitAction,exit,H_Inv80_b6ff_R2_0_I3,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv1922_5e75_R2_0_I3
THEOREM L_19 == TypeOK /\ H_Inv4227_eecc_R10_0_I3 /\ H_Inv4227_eecc_R10_0_I3 /\ H_Inv80_b6ff_R2_0_I3 /\ H_Inv1922_5e75_R2_0_I3 /\ Next => H_Inv1922_5e75_R2_0_I3'
  <1>. USE A0
  \* (H_Inv1922_5e75_R2_0_I3,ncsAction)
  <1>1. TypeOK /\ H_Inv1922_5e75_R2_0_I3 /\ ncsAction => H_Inv1922_5e75_R2_0_I3' BY DEF TypeOK,ncsAction,ncs,H_Inv1922_5e75_R2_0_I3,\prec
  \* (H_Inv1922_5e75_R2_0_I3,e1aAction)
  <1>2. TypeOK /\ H_Inv1922_5e75_R2_0_I3 /\ e1aAction => H_Inv1922_5e75_R2_0_I3' BY DEF TypeOK,e1aAction,e1a,H_Inv1922_5e75_R2_0_I3,\prec
  \* (H_Inv1922_5e75_R2_0_I3,e1bAction)
  <1>3. TypeOK /\ H_Inv1922_5e75_R2_0_I3 /\ e1bAction => H_Inv1922_5e75_R2_0_I3' BY DEF TypeOK,e1bAction,e1b,H_Inv1922_5e75_R2_0_I3,\prec
  \* (H_Inv1922_5e75_R2_0_I3,e2aAction)
  <1>4. TypeOK /\ H_Inv1922_5e75_R2_0_I3 /\ e2aAction => H_Inv1922_5e75_R2_0_I3' BY DEF TypeOK,e2aAction,e2a,H_Inv1922_5e75_R2_0_I3,\prec,Procs
  \* (H_Inv1922_5e75_R2_0_I3,e2bAction)
  <1>5. TypeOK /\ H_Inv1922_5e75_R2_0_I3 /\ e2bAction => H_Inv1922_5e75_R2_0_I3' BY DEF TypeOK,e2bAction,e2b,H_Inv1922_5e75_R2_0_I3,\prec
  \* (H_Inv1922_5e75_R2_0_I3,e3aAction)
  <1>6. TypeOK /\ H_Inv1922_5e75_R2_0_I3 /\ e3aAction => H_Inv1922_5e75_R2_0_I3' BY DEF TypeOK,e3aAction,e3a,H_Inv1922_5e75_R2_0_I3,\prec
  \* (H_Inv1922_5e75_R2_0_I3,e3bAction)
  <1>7. TypeOK /\ H_Inv1922_5e75_R2_0_I3 /\ e3bAction => H_Inv1922_5e75_R2_0_I3' BY DEF TypeOK,e3bAction,e3b,H_Inv1922_5e75_R2_0_I3,\prec,\prec
  \* (H_Inv1922_5e75_R2_0_I3,e4aAction)
  <1>8. TypeOK /\ H_Inv1922_5e75_R2_0_I3 /\ e4aAction => H_Inv1922_5e75_R2_0_I3' BY DEF TypeOK,e4aAction,e4a,H_Inv1922_5e75_R2_0_I3,\prec
  \* (H_Inv1922_5e75_R2_0_I3,e4bAction)
  <1>9. TypeOK /\ H_Inv4227_eecc_R10_0_I3 /\ H_Inv1922_5e75_R2_0_I3 /\ e4bAction => H_Inv1922_5e75_R2_0_I3' BY DEF TypeOK,H_Inv4227_eecc_R10_0_I3,e4bAction,e4b,H_Inv1922_5e75_R2_0_I3,\prec,\prec
  \* (H_Inv1922_5e75_R2_0_I3,w1aAction)
  <1>10. TypeOK /\ H_Inv1922_5e75_R2_0_I3 /\ w1aAction => H_Inv1922_5e75_R2_0_I3' BY DEF TypeOK,w1aAction,w1a,H_Inv1922_5e75_R2_0_I3,\prec,\prec
  \* (H_Inv1922_5e75_R2_0_I3,w1bAction)
  <1>11. TypeOK /\ H_Inv1922_5e75_R2_0_I3 /\ w1bAction => H_Inv1922_5e75_R2_0_I3' BY DEF TypeOK,w1bAction,w1b,H_Inv1922_5e75_R2_0_I3,\prec,\prec
  \* (H_Inv1922_5e75_R2_0_I3,w2Action)
  <1>12. TypeOK /\ H_Inv4227_eecc_R10_0_I3 /\ H_Inv80_b6ff_R2_0_I3 /\ H_Inv1922_5e75_R2_0_I3 /\ w2Action => H_Inv1922_5e75_R2_0_I3' BY DEF TypeOK,H_Inv4227_eecc_R10_0_I3,H_Inv80_b6ff_R2_0_I3,w2Action,w2,H_Inv1922_5e75_R2_0_I3,\prec,\prec
  \* (H_Inv1922_5e75_R2_0_I3,csAction)
  <1>13. TypeOK /\ H_Inv1922_5e75_R2_0_I3 /\ csAction => H_Inv1922_5e75_R2_0_I3' BY DEF TypeOK,csAction,cs,H_Inv1922_5e75_R2_0_I3,\prec
  \* (H_Inv1922_5e75_R2_0_I3,exitAction)
  <1>14. TypeOK /\ H_Inv1922_5e75_R2_0_I3 /\ exitAction => H_Inv1922_5e75_R2_0_I3' BY DEF TypeOK,exitAction,exit,H_Inv1922_5e75_R2_0_I3,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv4606_2f6b_R5_0_I2
THEOREM L_20 == TypeOK /\ H_Inv32498_2818_R11_0_I2 /\ H_Inv4227_eecc_R10_0_I3 /\ H_Inv4606_2f6b_R5_0_I2 /\ Next => H_Inv4606_2f6b_R5_0_I2'
  <1>. USE A0
  \* (H_Inv4606_2f6b_R5_0_I2,ncsAction)
  <1>1. TypeOK /\ H_Inv4606_2f6b_R5_0_I2 /\ ncsAction => H_Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,ncsAction,ncs,H_Inv4606_2f6b_R5_0_I2,\prec
  \* (H_Inv4606_2f6b_R5_0_I2,e1aAction)
  <1>2. TypeOK /\ H_Inv4606_2f6b_R5_0_I2 /\ e1aAction => H_Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,e1aAction,e1a,H_Inv4606_2f6b_R5_0_I2,\prec
  \* (H_Inv4606_2f6b_R5_0_I2,e1bAction)
  <1>3. TypeOK /\ H_Inv4606_2f6b_R5_0_I2 /\ e1bAction => H_Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,e1bAction,e1b,H_Inv4606_2f6b_R5_0_I2,\prec
  \* (H_Inv4606_2f6b_R5_0_I2,e2aAction)
  <1>4. TypeOK /\ H_Inv4606_2f6b_R5_0_I2 /\ e2aAction => H_Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,e2aAction,e2a,H_Inv4606_2f6b_R5_0_I2,\prec,Procs
  \* (H_Inv4606_2f6b_R5_0_I2,e2bAction)
  <1>5. TypeOK /\ H_Inv4606_2f6b_R5_0_I2 /\ e2bAction => H_Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,e2bAction,e2b,H_Inv4606_2f6b_R5_0_I2,\prec
  \* (H_Inv4606_2f6b_R5_0_I2,e3aAction)
  <1>6. TypeOK /\ H_Inv4606_2f6b_R5_0_I2 /\ e3aAction => H_Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,e3aAction,e3a,H_Inv4606_2f6b_R5_0_I2,\prec
  \* (H_Inv4606_2f6b_R5_0_I2,e3bAction)
  <1>7. TypeOK /\ H_Inv32498_2818_R11_0_I2 /\ H_Inv4606_2f6b_R5_0_I2 /\ e3bAction => H_Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,H_Inv32498_2818_R11_0_I2,e3bAction,e3b,H_Inv4606_2f6b_R5_0_I2,\prec,\prec
  \* (H_Inv4606_2f6b_R5_0_I2,e4aAction)
  <1>8. TypeOK /\ H_Inv4606_2f6b_R5_0_I2 /\ e4aAction => H_Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,e4aAction,e4a,H_Inv4606_2f6b_R5_0_I2,\prec
  \* (H_Inv4606_2f6b_R5_0_I2,e4bAction)
  <1>9. TypeOK /\ H_Inv4606_2f6b_R5_0_I2 /\ e4bAction => H_Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,e4bAction,e4b,H_Inv4606_2f6b_R5_0_I2,\prec,\prec
  \* (H_Inv4606_2f6b_R5_0_I2,w1aAction)
  <1>10. TypeOK /\ H_Inv4606_2f6b_R5_0_I2 /\ w1aAction => H_Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,w1aAction,w1a,H_Inv4606_2f6b_R5_0_I2,\prec,\prec
  \* (H_Inv4606_2f6b_R5_0_I2,w1bAction)
  <1>11. TypeOK /\ H_Inv4227_eecc_R10_0_I3 /\ H_Inv4606_2f6b_R5_0_I2 /\ w1bAction => H_Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,H_Inv4227_eecc_R10_0_I3,w1bAction,w1b,H_Inv4606_2f6b_R5_0_I2,\prec,\prec
  \* (H_Inv4606_2f6b_R5_0_I2,w2Action)
  <1>12. TypeOK /\ H_Inv4606_2f6b_R5_0_I2 /\ w2Action => H_Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,w2Action,w2,H_Inv4606_2f6b_R5_0_I2,\prec,\prec
  \* (H_Inv4606_2f6b_R5_0_I2,csAction)
  <1>13. TypeOK /\ H_Inv4606_2f6b_R5_0_I2 /\ csAction => H_Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,csAction,cs,H_Inv4606_2f6b_R5_0_I2,\prec
  \* (H_Inv4606_2f6b_R5_0_I2,exitAction)
  <1>14. TypeOK /\ H_Inv4606_2f6b_R5_0_I2 /\ exitAction => H_Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,exitAction,exit,H_Inv4606_2f6b_R5_0_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv4520_48f3_R1_0_I2
THEOREM L_21 == TypeOK /\ H_Inv10_8778_R2_0_I3 /\ H_Inv5742_3d78_R2_0_I3 /\ H_Inv1922_5e75_R2_0_I3 /\ H_Inv80_b6ff_R2_0_I3 /\ H_Inv4520_48f3_R1_0_I2 /\ Next => H_Inv4520_48f3_R1_0_I2'
  <1>. USE A0
  \* (H_Inv4520_48f3_R1_0_I2,ncsAction)
  <1>1. TypeOK /\ H_Inv4520_48f3_R1_0_I2 /\ ncsAction => H_Inv4520_48f3_R1_0_I2' BY DEF TypeOK,ncsAction,ncs,H_Inv4520_48f3_R1_0_I2,\prec
  \* (H_Inv4520_48f3_R1_0_I2,e1aAction)
  <1>2. TypeOK /\ H_Inv4520_48f3_R1_0_I2 /\ e1aAction => H_Inv4520_48f3_R1_0_I2' BY DEF TypeOK,e1aAction,e1a,H_Inv4520_48f3_R1_0_I2,\prec
  \* (H_Inv4520_48f3_R1_0_I2,e1bAction)
  <1>3. TypeOK /\ H_Inv4520_48f3_R1_0_I2 /\ e1bAction => H_Inv4520_48f3_R1_0_I2' BY DEF TypeOK,e1bAction,e1b,H_Inv4520_48f3_R1_0_I2,\prec
  \* (H_Inv4520_48f3_R1_0_I2,e2aAction)
  <1>4. TypeOK /\ H_Inv4520_48f3_R1_0_I2 /\ e2aAction => H_Inv4520_48f3_R1_0_I2' BY DEF TypeOK,e2aAction,e2a,H_Inv4520_48f3_R1_0_I2,\prec,Procs
  \* (H_Inv4520_48f3_R1_0_I2,e2bAction)
  <1>5. TypeOK /\ H_Inv4520_48f3_R1_0_I2 /\ e2bAction => H_Inv4520_48f3_R1_0_I2' BY DEF TypeOK,e2bAction,e2b,H_Inv4520_48f3_R1_0_I2,\prec
  \* (H_Inv4520_48f3_R1_0_I2,e3aAction)
  <1>6. TypeOK /\ H_Inv4520_48f3_R1_0_I2 /\ e3aAction => H_Inv4520_48f3_R1_0_I2' BY DEF TypeOK,e3aAction,e3a,H_Inv4520_48f3_R1_0_I2,\prec
  \* (H_Inv4520_48f3_R1_0_I2,e3bAction)
  <1>7. TypeOK /\ H_Inv4520_48f3_R1_0_I2 /\ e3bAction => H_Inv4520_48f3_R1_0_I2' BY DEF TypeOK,e3bAction,e3b,H_Inv4520_48f3_R1_0_I2,\prec,\prec
  \* (H_Inv4520_48f3_R1_0_I2,e4aAction)
  <1>8. TypeOK /\ H_Inv4520_48f3_R1_0_I2 /\ e4aAction => H_Inv4520_48f3_R1_0_I2' BY DEF TypeOK,e4aAction,e4a,H_Inv4520_48f3_R1_0_I2,\prec
  \* (H_Inv4520_48f3_R1_0_I2,e4bAction)
  <1>9. TypeOK /\ H_Inv4520_48f3_R1_0_I2 /\ e4bAction => H_Inv4520_48f3_R1_0_I2' BY DEF TypeOK,e4bAction,e4b,H_Inv4520_48f3_R1_0_I2,\prec,\prec
  \* (H_Inv4520_48f3_R1_0_I2,w1aAction)
  <1>10. TypeOK /\ H_Inv4520_48f3_R1_0_I2 /\ w1aAction => H_Inv4520_48f3_R1_0_I2' BY DEF TypeOK,w1aAction,w1a,H_Inv4520_48f3_R1_0_I2,\prec,\prec
  \* (H_Inv4520_48f3_R1_0_I2,w1bAction)
  <1>11. TypeOK /\ H_Inv4520_48f3_R1_0_I2 /\ w1bAction => H_Inv4520_48f3_R1_0_I2' BY DEF TypeOK,w1bAction,w1b,H_Inv4520_48f3_R1_0_I2,\prec,\prec
  \* (H_Inv4520_48f3_R1_0_I2,w2Action)
  <1>12. TypeOK /\ H_Inv10_8778_R2_0_I3 /\ H_Inv5742_3d78_R2_0_I3 /\ H_Inv1922_5e75_R2_0_I3 /\ H_Inv80_b6ff_R2_0_I3 /\ H_Inv4520_48f3_R1_0_I2 /\ w2Action => H_Inv4520_48f3_R1_0_I2' BY DEF TypeOK,H_Inv10_8778_R2_0_I3,H_Inv5742_3d78_R2_0_I3,H_Inv1922_5e75_R2_0_I3,H_Inv80_b6ff_R2_0_I3,w2Action,w2,H_Inv4520_48f3_R1_0_I2,\prec,\prec
  \* (H_Inv4520_48f3_R1_0_I2,csAction)
  <1>13. TypeOK /\ H_Inv4520_48f3_R1_0_I2 /\ csAction => H_Inv4520_48f3_R1_0_I2' BY DEF TypeOK,csAction,cs,H_Inv4520_48f3_R1_0_I2,\prec
  \* (H_Inv4520_48f3_R1_0_I2,exitAction)
  <1>14. TypeOK /\ H_Inv4520_48f3_R1_0_I2 /\ exitAction => H_Inv4520_48f3_R1_0_I2' BY DEF TypeOK,exitAction,exit,H_Inv4520_48f3_R1_0_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv4521_3f08_R1_1_I2
THEOREM L_22 == TypeOK /\ H_Inv80_b6ff_R2_0_I3 /\ H_Inv4521_3f08_R1_1_I2 /\ Next => H_Inv4521_3f08_R1_1_I2'
  <1>. USE A0
  \* (H_Inv4521_3f08_R1_1_I2,ncsAction)
  <1>1. TypeOK /\ H_Inv4521_3f08_R1_1_I2 /\ ncsAction => H_Inv4521_3f08_R1_1_I2' BY DEF TypeOK,ncsAction,ncs,H_Inv4521_3f08_R1_1_I2,\prec
  \* (H_Inv4521_3f08_R1_1_I2,e1aAction)
  <1>2. TypeOK /\ H_Inv4521_3f08_R1_1_I2 /\ e1aAction => H_Inv4521_3f08_R1_1_I2' BY DEF TypeOK,e1aAction,e1a,H_Inv4521_3f08_R1_1_I2,\prec
  \* (H_Inv4521_3f08_R1_1_I2,e1bAction)
  <1>3. TypeOK /\ H_Inv4521_3f08_R1_1_I2 /\ e1bAction => H_Inv4521_3f08_R1_1_I2' BY DEF TypeOK,e1bAction,e1b,H_Inv4521_3f08_R1_1_I2,\prec
  \* (H_Inv4521_3f08_R1_1_I2,e2aAction)
  <1>4. TypeOK /\ H_Inv4521_3f08_R1_1_I2 /\ e2aAction => H_Inv4521_3f08_R1_1_I2' BY DEF TypeOK,e2aAction,e2a,H_Inv4521_3f08_R1_1_I2,\prec,Procs
  \* (H_Inv4521_3f08_R1_1_I2,e2bAction)
  <1>5. TypeOK /\ H_Inv4521_3f08_R1_1_I2 /\ e2bAction => H_Inv4521_3f08_R1_1_I2' BY DEF TypeOK,e2bAction,e2b,H_Inv4521_3f08_R1_1_I2,\prec
  \* (H_Inv4521_3f08_R1_1_I2,e3aAction)
  <1>6. TypeOK /\ H_Inv4521_3f08_R1_1_I2 /\ e3aAction => H_Inv4521_3f08_R1_1_I2' BY DEF TypeOK,e3aAction,e3a,H_Inv4521_3f08_R1_1_I2,\prec
  \* (H_Inv4521_3f08_R1_1_I2,e3bAction)
  <1>7. TypeOK /\ H_Inv4521_3f08_R1_1_I2 /\ e3bAction => H_Inv4521_3f08_R1_1_I2' BY DEF TypeOK,e3bAction,e3b,H_Inv4521_3f08_R1_1_I2,\prec,\prec
  \* (H_Inv4521_3f08_R1_1_I2,e4aAction)
  <1>8. TypeOK /\ H_Inv4521_3f08_R1_1_I2 /\ e4aAction => H_Inv4521_3f08_R1_1_I2' BY DEF TypeOK,e4aAction,e4a,H_Inv4521_3f08_R1_1_I2,\prec
  \* (H_Inv4521_3f08_R1_1_I2,e4bAction)
  <1>9. TypeOK /\ H_Inv4521_3f08_R1_1_I2 /\ e4bAction => H_Inv4521_3f08_R1_1_I2' BY DEF TypeOK,e4bAction,e4b,H_Inv4521_3f08_R1_1_I2,\prec,\prec
  \* (H_Inv4521_3f08_R1_1_I2,w1aAction)
  <1>10. TypeOK /\ H_Inv4521_3f08_R1_1_I2 /\ w1aAction => H_Inv4521_3f08_R1_1_I2' BY DEF TypeOK,w1aAction,w1a,H_Inv4521_3f08_R1_1_I2,\prec,\prec
  \* (H_Inv4521_3f08_R1_1_I2,w1bAction)
  <1>11. TypeOK /\ H_Inv80_b6ff_R2_0_I3 /\ H_Inv4521_3f08_R1_1_I2 /\ w1bAction => H_Inv4521_3f08_R1_1_I2' BY DEF TypeOK,H_Inv80_b6ff_R2_0_I3,w1bAction,w1b,H_Inv4521_3f08_R1_1_I2,\prec,\prec
  \* (H_Inv4521_3f08_R1_1_I2,w2Action)
  <1>12. TypeOK /\ H_Inv4521_3f08_R1_1_I2 /\ w2Action => H_Inv4521_3f08_R1_1_I2' BY DEF TypeOK,w2Action,w2,H_Inv4521_3f08_R1_1_I2,\prec,\prec
  \* (H_Inv4521_3f08_R1_1_I2,csAction)
  <1>13. TypeOK /\ H_Inv4521_3f08_R1_1_I2 /\ csAction => H_Inv4521_3f08_R1_1_I2' BY DEF TypeOK,csAction,cs,H_Inv4521_3f08_R1_1_I2,\prec
  \* (H_Inv4521_3f08_R1_1_I2,exitAction)
  <1>14. TypeOK /\ H_Inv4521_3f08_R1_1_I2 /\ exitAction => H_Inv4521_3f08_R1_1_I2' BY DEF TypeOK,exitAction,exit,H_Inv4521_3f08_R1_1_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv5819_32cd_R1_1_I2
THEOREM L_23 == TypeOK /\ H_Inv4690_2f61_R0_0_I2 /\ H_Inv4520_48f3_R1_0_I2 /\ H_Inv5819_32cd_R1_1_I2 /\ Next => H_Inv5819_32cd_R1_1_I2'
  <1>. USE A0
  \* (H_Inv5819_32cd_R1_1_I2,ncsAction)
  <1>1. TypeOK /\ H_Inv5819_32cd_R1_1_I2 /\ ncsAction => H_Inv5819_32cd_R1_1_I2' BY DEF TypeOK,ncsAction,ncs,H_Inv5819_32cd_R1_1_I2,\prec
  \* (H_Inv5819_32cd_R1_1_I2,e1aAction)
  <1>2. TypeOK /\ H_Inv5819_32cd_R1_1_I2 /\ e1aAction => H_Inv5819_32cd_R1_1_I2' BY DEF TypeOK,e1aAction,e1a,H_Inv5819_32cd_R1_1_I2,\prec
  \* (H_Inv5819_32cd_R1_1_I2,e1bAction)
  <1>3. TypeOK /\ H_Inv5819_32cd_R1_1_I2 /\ e1bAction => H_Inv5819_32cd_R1_1_I2' BY DEF TypeOK,e1bAction,e1b,H_Inv5819_32cd_R1_1_I2,\prec
  \* (H_Inv5819_32cd_R1_1_I2,e2aAction)
  <1>4. TypeOK /\ H_Inv5819_32cd_R1_1_I2 /\ e2aAction => H_Inv5819_32cd_R1_1_I2' BY DEF TypeOK,e2aAction,e2a,H_Inv5819_32cd_R1_1_I2,\prec,Procs
  \* (H_Inv5819_32cd_R1_1_I2,e2bAction)
  <1>5. TypeOK /\ H_Inv5819_32cd_R1_1_I2 /\ e2bAction => H_Inv5819_32cd_R1_1_I2' BY DEF TypeOK,e2bAction,e2b,H_Inv5819_32cd_R1_1_I2,\prec
  \* (H_Inv5819_32cd_R1_1_I2,e3aAction)
  <1>6. TypeOK /\ H_Inv5819_32cd_R1_1_I2 /\ e3aAction => H_Inv5819_32cd_R1_1_I2' BY DEF TypeOK,e3aAction,e3a,H_Inv5819_32cd_R1_1_I2,\prec
  \* (H_Inv5819_32cd_R1_1_I2,e3bAction)
  <1>7. TypeOK /\ H_Inv5819_32cd_R1_1_I2 /\ e3bAction => H_Inv5819_32cd_R1_1_I2' BY DEF TypeOK,e3bAction,e3b,H_Inv5819_32cd_R1_1_I2,\prec,\prec
  \* (H_Inv5819_32cd_R1_1_I2,e4aAction)
  <1>8. TypeOK /\ H_Inv5819_32cd_R1_1_I2 /\ e4aAction => H_Inv5819_32cd_R1_1_I2' BY DEF TypeOK,e4aAction,e4a,H_Inv5819_32cd_R1_1_I2,\prec
  \* (H_Inv5819_32cd_R1_1_I2,e4bAction)
  <1>9. TypeOK /\ H_Inv5819_32cd_R1_1_I2 /\ e4bAction => H_Inv5819_32cd_R1_1_I2' BY DEF TypeOK,e4bAction,e4b,H_Inv5819_32cd_R1_1_I2,\prec,\prec
  \* (H_Inv5819_32cd_R1_1_I2,w1aAction)
  <1>10. TypeOK /\ H_Inv4690_2f61_R0_0_I2 /\ H_Inv5819_32cd_R1_1_I2 /\ w1aAction => H_Inv5819_32cd_R1_1_I2' BY DEF TypeOK,H_Inv4690_2f61_R0_0_I2,w1aAction,w1a,H_Inv5819_32cd_R1_1_I2,\prec,\prec
  \* (H_Inv5819_32cd_R1_1_I2,w1bAction)
  <1>11. TypeOK /\ H_Inv4520_48f3_R1_0_I2 /\ H_Inv5819_32cd_R1_1_I2 /\ w1bAction => H_Inv5819_32cd_R1_1_I2' BY DEF TypeOK,H_Inv4520_48f3_R1_0_I2,w1bAction,w1b,H_Inv5819_32cd_R1_1_I2,\prec,\prec
  \* (H_Inv5819_32cd_R1_1_I2,w2Action)
  <1>12. TypeOK /\ H_Inv5819_32cd_R1_1_I2 /\ w2Action => H_Inv5819_32cd_R1_1_I2' BY DEF TypeOK,w2Action,w2,H_Inv5819_32cd_R1_1_I2,\prec,\prec
  \* (H_Inv5819_32cd_R1_1_I2,csAction)
  <1>13. TypeOK /\ H_Inv5819_32cd_R1_1_I2 /\ csAction => H_Inv5819_32cd_R1_1_I2' BY DEF TypeOK,csAction,cs,H_Inv5819_32cd_R1_1_I2,\prec
  \* (H_Inv5819_32cd_R1_1_I2,exitAction)
  <1>14. TypeOK /\ H_Inv5819_32cd_R1_1_I2 /\ exitAction => H_Inv5819_32cd_R1_1_I2' BY DEF TypeOK,exitAction,exit,H_Inv5819_32cd_R1_1_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv24959_7f87_R1_1_I2
THEOREM L_24 == TypeOK /\ H_Inv24959_7f87_R1_1_I2 /\ Next => H_Inv24959_7f87_R1_1_I2'
  <1>. USE A0
  \* (H_Inv24959_7f87_R1_1_I2,ncsAction)
  <1>1. TypeOK /\ H_Inv24959_7f87_R1_1_I2 /\ ncsAction => H_Inv24959_7f87_R1_1_I2' BY DEF TypeOK,ncsAction,ncs,H_Inv24959_7f87_R1_1_I2,\prec
  \* (H_Inv24959_7f87_R1_1_I2,e1aAction)
  <1>2. TypeOK /\ H_Inv24959_7f87_R1_1_I2 /\ e1aAction => H_Inv24959_7f87_R1_1_I2' BY DEF TypeOK,e1aAction,e1a,H_Inv24959_7f87_R1_1_I2,\prec
  \* (H_Inv24959_7f87_R1_1_I2,e1bAction)
  <1>3. TypeOK /\ H_Inv24959_7f87_R1_1_I2 /\ e1bAction => H_Inv24959_7f87_R1_1_I2' BY DEF TypeOK,e1bAction,e1b,H_Inv24959_7f87_R1_1_I2,\prec
  \* (H_Inv24959_7f87_R1_1_I2,e2aAction)
  <1>4. TypeOK /\ H_Inv24959_7f87_R1_1_I2 /\ e2aAction => H_Inv24959_7f87_R1_1_I2' BY DEF TypeOK,e2aAction,e2a,H_Inv24959_7f87_R1_1_I2,\prec,Procs
  \* (H_Inv24959_7f87_R1_1_I2,e2bAction)
  <1>5. TypeOK /\ H_Inv24959_7f87_R1_1_I2 /\ e2bAction => H_Inv24959_7f87_R1_1_I2' BY DEF TypeOK,e2bAction,e2b,H_Inv24959_7f87_R1_1_I2,\prec
  \* (H_Inv24959_7f87_R1_1_I2,e3aAction)
  <1>6. TypeOK /\ H_Inv24959_7f87_R1_1_I2 /\ e3aAction => H_Inv24959_7f87_R1_1_I2' BY DEF TypeOK,e3aAction,e3a,H_Inv24959_7f87_R1_1_I2,\prec
  \* (H_Inv24959_7f87_R1_1_I2,e3bAction)
  <1>7. TypeOK /\ H_Inv24959_7f87_R1_1_I2 /\ e3bAction => H_Inv24959_7f87_R1_1_I2' BY DEF TypeOK,e3bAction,e3b,H_Inv24959_7f87_R1_1_I2,\prec,\prec
  \* (H_Inv24959_7f87_R1_1_I2,e4aAction)
  <1>8. TypeOK /\ H_Inv24959_7f87_R1_1_I2 /\ e4aAction => H_Inv24959_7f87_R1_1_I2' BY DEF TypeOK,e4aAction,e4a,H_Inv24959_7f87_R1_1_I2,\prec
  \* (H_Inv24959_7f87_R1_1_I2,e4bAction)
  <1>9. TypeOK /\ H_Inv24959_7f87_R1_1_I2 /\ e4bAction => H_Inv24959_7f87_R1_1_I2' BY DEF TypeOK,e4bAction,e4b,H_Inv24959_7f87_R1_1_I2,\prec,\prec
  \* (H_Inv24959_7f87_R1_1_I2,w1aAction)
  <1>10. TypeOK /\ H_Inv24959_7f87_R1_1_I2 /\ w1aAction => H_Inv24959_7f87_R1_1_I2' BY DEF TypeOK,w1aAction,w1a,H_Inv24959_7f87_R1_1_I2,\prec,\prec
  \* (H_Inv24959_7f87_R1_1_I2,w1bAction)
  <1>11. TypeOK /\ H_Inv24959_7f87_R1_1_I2 /\ w1bAction => H_Inv24959_7f87_R1_1_I2' BY DEF TypeOK,w1bAction,w1b,H_Inv24959_7f87_R1_1_I2,\prec,\prec
  \* (H_Inv24959_7f87_R1_1_I2,w2Action)
  <1>12. TypeOK /\ H_Inv24959_7f87_R1_1_I2 /\ w2Action => H_Inv24959_7f87_R1_1_I2' BY DEF TypeOK,w2Action,w2,H_Inv24959_7f87_R1_1_I2,\prec,\prec
  \* (H_Inv24959_7f87_R1_1_I2,csAction)
  <1>13. TypeOK /\ H_Inv24959_7f87_R1_1_I2 /\ csAction => H_Inv24959_7f87_R1_1_I2' BY DEF TypeOK,csAction,cs,H_Inv24959_7f87_R1_1_I2,\prec
  \* (H_Inv24959_7f87_R1_1_I2,exitAction)
  <1>14. TypeOK /\ H_Inv24959_7f87_R1_1_I2 /\ exitAction => H_Inv24959_7f87_R1_1_I2' BY DEF TypeOK,exitAction,exit,H_Inv24959_7f87_R1_1_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv4576_59b1_R1_1_I2
THEOREM L_25 == TypeOK /\ H_Inv4606_2f6b_R5_0_I2 /\ H_Inv1922_5e75_R2_0_I3 /\ H_Inv4576_59b1_R1_1_I2 /\ Next => H_Inv4576_59b1_R1_1_I2'
  <1>. USE A0
  \* (H_Inv4576_59b1_R1_1_I2,ncsAction)
  <1>1. TypeOK /\ H_Inv4576_59b1_R1_1_I2 /\ ncsAction => H_Inv4576_59b1_R1_1_I2' BY DEF TypeOK,ncsAction,ncs,H_Inv4576_59b1_R1_1_I2,\prec
  \* (H_Inv4576_59b1_R1_1_I2,e1aAction)
  <1>2. TypeOK /\ H_Inv4576_59b1_R1_1_I2 /\ e1aAction => H_Inv4576_59b1_R1_1_I2' BY DEF TypeOK,e1aAction,e1a,H_Inv4576_59b1_R1_1_I2,\prec
  \* (H_Inv4576_59b1_R1_1_I2,e1bAction)
  <1>3. TypeOK /\ H_Inv4576_59b1_R1_1_I2 /\ e1bAction => H_Inv4576_59b1_R1_1_I2' BY DEF TypeOK,e1bAction,e1b,H_Inv4576_59b1_R1_1_I2,\prec
  \* (H_Inv4576_59b1_R1_1_I2,e2aAction)
  <1>4. TypeOK /\ H_Inv4576_59b1_R1_1_I2 /\ e2aAction => H_Inv4576_59b1_R1_1_I2' BY DEF TypeOK,e2aAction,e2a,H_Inv4576_59b1_R1_1_I2,\prec,Procs
  \* (H_Inv4576_59b1_R1_1_I2,e2bAction)
  <1>5. TypeOK /\ H_Inv4576_59b1_R1_1_I2 /\ e2bAction => H_Inv4576_59b1_R1_1_I2' BY DEF TypeOK,e2bAction,e2b,H_Inv4576_59b1_R1_1_I2,\prec
  \* (H_Inv4576_59b1_R1_1_I2,e3aAction)
  <1>6. TypeOK /\ H_Inv4576_59b1_R1_1_I2 /\ e3aAction => H_Inv4576_59b1_R1_1_I2' BY DEF TypeOK,e3aAction,e3a,H_Inv4576_59b1_R1_1_I2,\prec
  \* (H_Inv4576_59b1_R1_1_I2,e3bAction)
  <1>7. TypeOK /\ H_Inv4576_59b1_R1_1_I2 /\ e3bAction => H_Inv4576_59b1_R1_1_I2' BY DEF TypeOK,e3bAction,e3b,H_Inv4576_59b1_R1_1_I2,\prec,\prec
  \* (H_Inv4576_59b1_R1_1_I2,e4aAction)
  <1>8. TypeOK /\ H_Inv4576_59b1_R1_1_I2 /\ e4aAction => H_Inv4576_59b1_R1_1_I2' BY DEF TypeOK,e4aAction,e4a,H_Inv4576_59b1_R1_1_I2,\prec
  \* (H_Inv4576_59b1_R1_1_I2,e4bAction)
  <1>9. TypeOK /\ H_Inv4576_59b1_R1_1_I2 /\ e4bAction => H_Inv4576_59b1_R1_1_I2' BY DEF TypeOK,e4bAction,e4b,H_Inv4576_59b1_R1_1_I2,\prec,\prec
  \* (H_Inv4576_59b1_R1_1_I2,w1aAction)
  <1>10. TypeOK /\ H_Inv4606_2f6b_R5_0_I2 /\ H_Inv4576_59b1_R1_1_I2 /\ w1aAction => H_Inv4576_59b1_R1_1_I2' BY DEF TypeOK,H_Inv4606_2f6b_R5_0_I2,w1aAction,w1a,H_Inv4576_59b1_R1_1_I2,\prec,\prec
  \* (H_Inv4576_59b1_R1_1_I2,w1bAction)
  <1>11. TypeOK /\ H_Inv1922_5e75_R2_0_I3 /\ H_Inv4576_59b1_R1_1_I2 /\ w1bAction => H_Inv4576_59b1_R1_1_I2' BY DEF TypeOK,H_Inv1922_5e75_R2_0_I3,w1bAction,w1b,H_Inv4576_59b1_R1_1_I2,\prec,\prec
  \* (H_Inv4576_59b1_R1_1_I2,w2Action)
  <1>12. TypeOK /\ H_Inv4576_59b1_R1_1_I2 /\ w2Action => H_Inv4576_59b1_R1_1_I2' BY DEF TypeOK,w2Action,w2,H_Inv4576_59b1_R1_1_I2,\prec,\prec
  \* (H_Inv4576_59b1_R1_1_I2,csAction)
  <1>13. TypeOK /\ H_Inv4576_59b1_R1_1_I2 /\ csAction => H_Inv4576_59b1_R1_1_I2' BY DEF TypeOK,csAction,cs,H_Inv4576_59b1_R1_1_I2,\prec
  \* (H_Inv4576_59b1_R1_1_I2,exitAction)
  <1>14. TypeOK /\ H_Inv4576_59b1_R1_1_I2 /\ exitAction => H_Inv4576_59b1_R1_1_I2' BY DEF TypeOK,exitAction,exit,H_Inv4576_59b1_R1_1_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** H_Inv4690_2f61_R0_0_I2
THEOREM L_26 == TypeOK /\ H_Inv4520_48f3_R1_0_I2 /\ H_Inv4576_59b1_R1_1_I2 /\ H_Inv24959_7f87_R1_1_I2 /\ H_Inv5819_32cd_R1_1_I2 /\ H_Inv4521_3f08_R1_1_I2 /\ H_Inv4690_2f61_R0_0_I2 /\ Next => H_Inv4690_2f61_R0_0_I2'
  <1>. USE A0
  \* (H_Inv4690_2f61_R0_0_I2,ncsAction)
  <1>1. TypeOK /\ H_Inv4690_2f61_R0_0_I2 /\ ncsAction => H_Inv4690_2f61_R0_0_I2' BY DEF TypeOK,ncsAction,ncs,H_Inv4690_2f61_R0_0_I2,\prec
  \* (H_Inv4690_2f61_R0_0_I2,e1aAction)
  <1>2. TypeOK /\ H_Inv4690_2f61_R0_0_I2 /\ e1aAction => H_Inv4690_2f61_R0_0_I2' BY DEF TypeOK,e1aAction,e1a,H_Inv4690_2f61_R0_0_I2,\prec
  \* (H_Inv4690_2f61_R0_0_I2,e1bAction)
  <1>3. TypeOK /\ H_Inv4690_2f61_R0_0_I2 /\ e1bAction => H_Inv4690_2f61_R0_0_I2' BY DEF TypeOK,e1bAction,e1b,H_Inv4690_2f61_R0_0_I2,\prec
  \* (H_Inv4690_2f61_R0_0_I2,e2aAction)
  <1>4. TypeOK /\ H_Inv4690_2f61_R0_0_I2 /\ e2aAction => H_Inv4690_2f61_R0_0_I2' BY DEF TypeOK,e2aAction,e2a,H_Inv4690_2f61_R0_0_I2,\prec,Procs
  \* (H_Inv4690_2f61_R0_0_I2,e2bAction)
  <1>5. TypeOK /\ H_Inv4690_2f61_R0_0_I2 /\ e2bAction => H_Inv4690_2f61_R0_0_I2' BY DEF TypeOK,e2bAction,e2b,H_Inv4690_2f61_R0_0_I2,\prec
  \* (H_Inv4690_2f61_R0_0_I2,e3aAction)
  <1>6. TypeOK /\ H_Inv4690_2f61_R0_0_I2 /\ e3aAction => H_Inv4690_2f61_R0_0_I2' BY DEF TypeOK,e3aAction,e3a,H_Inv4690_2f61_R0_0_I2,\prec
  \* (H_Inv4690_2f61_R0_0_I2,e3bAction)
  <1>7. TypeOK /\ H_Inv4690_2f61_R0_0_I2 /\ e3bAction => H_Inv4690_2f61_R0_0_I2' BY DEF TypeOK,e3bAction,e3b,H_Inv4690_2f61_R0_0_I2,\prec,\prec
  \* (H_Inv4690_2f61_R0_0_I2,e4aAction)
  <1>8. TypeOK /\ H_Inv4690_2f61_R0_0_I2 /\ e4aAction => H_Inv4690_2f61_R0_0_I2' BY DEF TypeOK,e4aAction,e4a,H_Inv4690_2f61_R0_0_I2,\prec
  \* (H_Inv4690_2f61_R0_0_I2,e4bAction)
  <1>9. TypeOK /\ H_Inv4690_2f61_R0_0_I2 /\ e4bAction => H_Inv4690_2f61_R0_0_I2' BY DEF TypeOK,e4bAction,e4b,H_Inv4690_2f61_R0_0_I2,\prec,\prec
  \* (H_Inv4690_2f61_R0_0_I2,w1aAction)
  <1>10. TypeOK /\ H_Inv4690_2f61_R0_0_I2 /\ w1aAction => H_Inv4690_2f61_R0_0_I2' BY DEF TypeOK,w1aAction,w1a,H_Inv4690_2f61_R0_0_I2,\prec,\prec
  \* (H_Inv4690_2f61_R0_0_I2,w1bAction)
  <1>11. TypeOK /\ H_Inv4520_48f3_R1_0_I2 /\ H_Inv4690_2f61_R0_0_I2 /\ w1bAction => H_Inv4690_2f61_R0_0_I2' BY DEF TypeOK,H_Inv4520_48f3_R1_0_I2,w1bAction,w1b,H_Inv4690_2f61_R0_0_I2,\prec,\prec
  \* (H_Inv4690_2f61_R0_0_I2,w2Action)
  <1>12. TypeOK /\ H_Inv4576_59b1_R1_1_I2 /\ H_Inv24959_7f87_R1_1_I2 /\ H_Inv5819_32cd_R1_1_I2 /\ H_Inv4521_3f08_R1_1_I2 /\ H_Inv4690_2f61_R0_0_I2 /\ w2Action => H_Inv4690_2f61_R0_0_I2' BY DEF TypeOK,H_Inv4576_59b1_R1_1_I2,H_Inv24959_7f87_R1_1_I2,H_Inv5819_32cd_R1_1_I2,H_Inv4521_3f08_R1_1_I2,w2Action,w2,H_Inv4690_2f61_R0_0_I2,\prec,\prec
  \* (H_Inv4690_2f61_R0_0_I2,csAction)
  <1>13. TypeOK /\ H_Inv4690_2f61_R0_0_I2 /\ csAction => H_Inv4690_2f61_R0_0_I2' BY DEF TypeOK,csAction,cs,H_Inv4690_2f61_R0_0_I2,\prec
  \* (H_Inv4690_2f61_R0_0_I2,exitAction)
  <1>14. TypeOK /\ H_Inv4690_2f61_R0_0_I2 /\ exitAction => H_Inv4690_2f61_R0_0_I2' BY DEF TypeOK,exitAction,exit,H_Inv4690_2f61_R0_0_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* (ROOT SAFETY PROP)
\*** H_MutualExclusion
THEOREM L_27 == TypeOK /\ H_Inv4690_2f61_R0_0_I2 /\ H_MutualExclusion /\ Next => H_MutualExclusion'
  <1>. USE A0
  \* (H_MutualExclusion,ncsAction)
  <1>1. TypeOK /\ H_MutualExclusion /\ ncsAction => H_MutualExclusion' BY DEF TypeOK,ncsAction,ncs,H_MutualExclusion,\prec
  \* (H_MutualExclusion,e1aAction)
  <1>2. TypeOK /\ H_MutualExclusion /\ e1aAction => H_MutualExclusion' BY DEF TypeOK,e1aAction,e1a,H_MutualExclusion,\prec
  \* (H_MutualExclusion,e1bAction)
  <1>3. TypeOK /\ H_MutualExclusion /\ e1bAction => H_MutualExclusion' BY DEF TypeOK,e1bAction,e1b,H_MutualExclusion,\prec
  \* (H_MutualExclusion,e2aAction)
  <1>4. TypeOK /\ H_MutualExclusion /\ e2aAction => H_MutualExclusion' BY DEF TypeOK,e2aAction,e2a,H_MutualExclusion,\prec,Procs
  \* (H_MutualExclusion,e2bAction)
  <1>5. TypeOK /\ H_MutualExclusion /\ e2bAction => H_MutualExclusion' BY DEF TypeOK,e2bAction,e2b,H_MutualExclusion,\prec
  \* (H_MutualExclusion,e3aAction)
  <1>6. TypeOK /\ H_MutualExclusion /\ e3aAction => H_MutualExclusion' BY DEF TypeOK,e3aAction,e3a,H_MutualExclusion,\prec
  \* (H_MutualExclusion,e3bAction)
  <1>7. TypeOK /\ H_MutualExclusion /\ e3bAction => H_MutualExclusion' BY DEF TypeOK,e3bAction,e3b,H_MutualExclusion,\prec,\prec
  \* (H_MutualExclusion,e4aAction)
  <1>8. TypeOK /\ H_MutualExclusion /\ e4aAction => H_MutualExclusion' BY DEF TypeOK,e4aAction,e4a,H_MutualExclusion,\prec
  \* (H_MutualExclusion,e4bAction)
  <1>9. TypeOK /\ H_MutualExclusion /\ e4bAction => H_MutualExclusion' BY DEF TypeOK,e4bAction,e4b,H_MutualExclusion,\prec,\prec
  \* (H_MutualExclusion,w1aAction)
  <1>10. TypeOK /\ H_MutualExclusion /\ w1aAction => H_MutualExclusion' BY DEF TypeOK,w1aAction,w1a,H_MutualExclusion,\prec,\prec
  \* (H_MutualExclusion,w1bAction)
  <1>11. TypeOK /\ H_Inv4690_2f61_R0_0_I2 /\ H_MutualExclusion /\ w1bAction => H_MutualExclusion' BY DEF TypeOK,H_Inv4690_2f61_R0_0_I2,w1bAction,w1b,H_MutualExclusion,\prec,\prec
  \* (H_MutualExclusion,w2Action)
  <1>12. TypeOK /\ H_MutualExclusion /\ w2Action => H_MutualExclusion' BY DEF TypeOK,w2Action,w2,H_MutualExclusion,\prec,\prec
  \* (H_MutualExclusion,csAction)
  <1>13. TypeOK /\ H_MutualExclusion /\ csAction => H_MutualExclusion' BY DEF TypeOK,csAction,cs,H_MutualExclusion,\prec
  \* (H_MutualExclusion,exitAction)
  <1>14. TypeOK /\ H_MutualExclusion /\ exitAction => H_MutualExclusion' BY DEF TypeOK,exitAction,exit,H_MutualExclusion,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0
<1> USE DEF \prec
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => H_Inv40_180c_R24_0_I1 BY DEF Init, H_Inv40_180c_R24_0_I1, IndGlobal
    <1>2. Init => H_Inv103_c9b1_R21_1_I1 BY DEF Init, H_Inv103_c9b1_R21_1_I1, IndGlobal
    <1>3. Init => H_Inv350_b077_R20_1_I2 BY DEF Init, H_Inv350_b077_R20_1_I2, IndGlobal
    <1>4. Init => H_Inv1_b58a_R20_0_I1 BY DEF Init, H_Inv1_b58a_R20_0_I1, IndGlobal
    <1>5. Init => H_Inv19_037d_R19_0_I1 BY DEF Init, H_Inv19_037d_R19_0_I1, IndGlobal
    <1>6. Init => H_Inv6093_1c74_R18_1_I2 BY DEF Init, H_Inv6093_1c74_R18_1_I2, IndGlobal
    <1>7. Init => H_Inv0_b3ba_R18_0_I0 BY DEF Init, H_Inv0_b3ba_R18_0_I0, IndGlobal
    <1>8. Init => H_Inv3293_1a1e_R17_0_I3 BY DEF Init, H_Inv3293_1a1e_R17_0_I3, IndGlobal
    <1>9. Init => H_Inv2740_e784_R16_0_I3 BY DEF Init, H_Inv2740_e784_R16_0_I3, IndGlobal
    <1>10. Init => H_Inv1028_6ea5_R8_0_I2 BY DEF Init, H_Inv1028_6ea5_R8_0_I2, IndGlobal
    <1>11. Init => H_Inv61_df69_R8_0_I2 BY DEF Init, H_Inv61_df69_R8_0_I2, IndGlobal
    <1>12. Init => H_Inv11_3838_R8_0_I2 BY DEF Init, H_Inv11_3838_R8_0_I2, IndGlobal
    <1>13. Init => H_Inv140_f68c_R9_0_I1 BY DEF Init, H_Inv140_f68c_R9_0_I1, IndGlobal
    <1>14. Init => H_Inv4227_eecc_R10_0_I3 BY DEF Init, H_Inv4227_eecc_R10_0_I3, IndGlobal
    <1>15. Init => H_Inv32498_2818_R11_0_I2 BY DEF Init, H_Inv32498_2818_R11_0_I2, IndGlobal
    <1>16. Init => H_Inv5742_3d78_R2_0_I3 BY DEF Init, H_Inv5742_3d78_R2_0_I3, IndGlobal
    <1>17. Init => H_Inv10_8778_R2_0_I3 BY DEF Init, H_Inv10_8778_R2_0_I3, IndGlobal
    <1>18. Init => H_Inv80_b6ff_R2_0_I3 BY DEF Init, H_Inv80_b6ff_R2_0_I3, IndGlobal
    <1>19. Init => H_Inv1922_5e75_R2_0_I3 BY DEF Init, H_Inv1922_5e75_R2_0_I3, IndGlobal
    <1>20. Init => H_Inv4606_2f6b_R5_0_I2 BY DEF Init, H_Inv4606_2f6b_R5_0_I2, IndGlobal
    <1>21. Init => H_Inv4520_48f3_R1_0_I2 BY DEF Init, H_Inv4520_48f3_R1_0_I2, IndGlobal
    <1>22. Init => H_Inv4521_3f08_R1_1_I2 BY DEF Init, H_Inv4521_3f08_R1_1_I2, IndGlobal
    <1>23. Init => H_Inv5819_32cd_R1_1_I2 BY DEF Init, H_Inv5819_32cd_R1_1_I2, IndGlobal
    <1>24. Init => H_Inv24959_7f87_R1_1_I2 BY DEF Init, H_Inv24959_7f87_R1_1_I2, IndGlobal
    <1>25. Init => H_Inv4576_59b1_R1_1_I2 BY DEF Init, H_Inv4576_59b1_R1_1_I2, IndGlobal
    <1>26. Init => H_Inv4690_2f61_R0_0_I2 BY DEF Init, H_Inv4690_2f61_R0_0_I2, IndGlobal
    <1>27. Init => H_MutualExclusion BY DEF Init, H_MutualExclusion, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14,<1>15,<1>16,<1>17,<1>18,<1>19,<1>20,<1>21,<1>22,<1>23,<1>24,<1>25,<1>26,<1>27 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13,L_14,L_15,L_16,L_17,L_18,L_19,L_20,L_21,L_22,L_23,L_24,L_25,L_26,L_27 DEF Next, IndGlobal

====
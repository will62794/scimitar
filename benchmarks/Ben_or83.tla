------------------------------ MODULE Ben_or83 -----------------------------

EXTENDS FiniteSets, Integers, TLC

CONSTANTS
    \* Number of processes
    N,
    \* Max number of faulty
    T,
    \* Actual number of faulty
    F,
    \* Set of rounds (note that endive does not take 1..3)
    Rounds

\* Set of currect processes
Correct == 1..(N - F)
\* Set of faulty processes
Faulty == (N - F + 1)..N
\* Set of all processes
All == Correct \cup Faulty

\* Set of values to decide
Values == { 0, 1 }
\* Value to denote no decision
NoDecision == -1
\* Values and no decision
AllV == { -1, 0, 1 }
\* Possible steps
Steps == 1..3

-----------------------------------------------------------------------------

VARIABLES
  \* Current value for each process (x_P)
  value,
  \* Decision by a process
  decision,
  \* The round each process is on
  round,
  \* The step each process is on
  step,
  \* Set of type 1 messages by round
  type1,
  \* Set of type 2 D messages by round
  type2D,
  \* Set of type 2 ? messages by round
  type2Q

-----------------------------------------------------------------------------

Step1(p) ==
  /\ step[p] = 1
  /\ type1' = [ type1 EXCEPT ![round[p]][p] = value[p] ]
  /\ step' = [ step EXCEPT ![p] = 2 ]
  /\ UNCHANGED << value, decision, round, type2D, type2Q >>
  
Step2(p) ==
  /\ step[p] = 2
  /\ \E received \in SUBSET { pr \in All : type1[round[p]][pr] # NoDecision }:
        /\ Cardinality(received) >= N - T
        /\ \/ \E v \in Values:
                 /\ 2 * Cardinality({ pr \in received : type1[round[p]][pr] = v }) > N + T
                 /\ type2D' = [ type2D EXCEPT ![round[p]][p] = v ]
                 /\ type2Q' = type2Q
           \/ /\ \A v \in Values: 2 * Cardinality({ pr \in received : type1[round[p]][pr] = v }) <= N + T
              /\ type2Q' = [ type2Q EXCEPT ![round[p]][p] = TRUE ]   
              /\ type2D' = type2D   
  /\ step' = [ step EXCEPT ![p] = 3 ]
  /\ UNCHANGED << value, decision, round, type1 >>
  
Step3(p) ==
  /\ step[p] = 3
  /\ \E received \in SUBSET { pr \in All : type2D[round[p]][pr] # NoDecision \/
                                           type2Q[round[p]][pr] = TRUE }:
        /\ Cardinality(received) = N - T
        /\ LET weights == [ v \in Values |-> Cardinality({ pr \in received : type2D[round[p]][pr] = v })]
            IN
            \/ (\E v \in Values:
                 /\ weights[v] >= T + 1
                 /\ value' = [ value EXCEPT ![p] = v ]
                 /\ IF 2 * weights[v] > N + T
                    THEN decision' = [ decision EXCEPT ![p] = v ]
                    ELSE decision' = decision)
             \/ /\ (\A v \in Values: weights[v] < T + 1)
                /\ (\E nextV \in Values: value' = [ value EXCEPT ![p] = nextV ])
                /\ decision' = decision
  /\ round[p] + 1 \in Rounds
  /\ round' = [ round EXCEPT ![p] = round[p] + 1 ]
  /\ step' = [ step EXCEPT ![p] = 1 ]
  /\ UNCHANGED << type1, type2D, type2Q >>

-----------------------------------------------------------------------------

Init == 
  /\ N > 5 * T
  /\ T >= F
  /\ value \in [ Correct -> Values ]
  /\ decision = [ r \in Correct |-> NoDecision ]
  /\ round = [ r \in Correct |-> 1 ]
  /\ step = [ r \in Correct |-> 1 ]
  
  /\ type1 = [ r \in Rounds |-> [ p \in All |-> IF p \in Correct THEN NoDecision ELSE CHOOSE v \in AllV : TRUE] ]
  /\ type2D = [ r \in Rounds |-> [ p \in All |-> IF p \in Correct THEN NoDecision ELSE CHOOSE v \in AllV : TRUE] ]
  /\ type2Q = [ r \in Rounds |-> [ p \in All |-> IF p \in Correct THEN FALSE ELSE CHOOSE v \in BOOLEAN : TRUE] ]

Step1Action == \E p \in Correct: Step1(p)

Step2Action == \E p \in Correct: Step2(p)

Step3Action == \E p \in Correct: Step3(p)

Next == 
    \/ Step1Action
    \/ Step2Action
    \/ Step3Action

-----------------------------------------------------------------------------

TypeOK ==
  /\ N > 5 * T
  /\ T >= F
  /\ value \in [ Correct -> Values ]
  /\ decision \in [ Correct -> AllV ]
  /\ round \in [ Correct -> Rounds ]
  /\ step \in [ Correct -> Steps ]
  /\ type1 \in [ Rounds -> [ All -> AllV ] ]
  /\ type2D \in [ Rounds -> [ All -> AllV ] ]
  /\ type2Q \in [ Rounds -> [ All -> BOOLEAN ] ]
  /\ \A r \in Rounds: 
        { p \in All : type2D[r][p] # NoDecision 
                   /\ type2Q[r][p] = TRUE 
                   /\ p \in Correct } = {}
        
AgreementInv ==
    \A p1, p2 \in Correct: 
        decision[p1] # NoDecision /\ decision[p2] # NoDecision
     => decision[p1] = decision[p2]


CTICost == 0
NextUnchanged == UNCHANGED << value, decision, round, step, type1, type2D, type2Q >>

=============================================================================
\* Modification History
\* Last modified Mon Jan 13 21:05:43 AEDT 2025 by breloom
\* Created Mon Jan 13 09:53:05 AEDT 2025 by breloom

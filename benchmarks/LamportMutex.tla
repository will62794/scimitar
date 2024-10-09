--------------------------- MODULE LamportMutex ----------------------------
(***************************************************************************)
(* TLA+ specification of Lamport's distributed mutual-exclusion algorithm  *)
(* that appeared as an example in                                          *)
(* L. Lamport:  Time, Clocks and the Ordering of Events in a Distributed   *)
(* System. CACM 21(7):558-565, 1978.                                       *)
(***************************************************************************)
EXTENDS Naturals, Sequences, TLC, Randomization, FiniteSets

(***************************************************************************)
(* The parameter N represents the number of processes.                     *)
(* The parameter maxClock is used only for model checking in order to      *)
(* keep the state space finite.                                            *)
(***************************************************************************)
CONSTANT N, maxClock
CONSTANT Nats

ASSUME NType == N \in Nat
ASSUME maxClockType == maxClock \in Nat

Proc == 1 .. N
\* Clock == Nat \ {0}
Clock == Nats \ {0}
(***************************************************************************)
(* For model checking, add ClockConstraint as a state constraint to ensure *)
(* a finite state space and override the definition of Clock by            *)
(* 1 .. maxClock+1 so that TLC can evaluate the definition of Message.     *)
(***************************************************************************)

VARIABLES
  clock,    \* local clock of each process
  req,      \* requests received from processes (clock transmitted with request)
  ack,      \* acknowledgements received from processes
  network,  \* messages sent but not yet received
  crit      \* set of processes in critical section

(***************************************************************************)
(* Messages used in the algorithm.                                         *)
(***************************************************************************)
ReqMessage(c) == [type |-> "req", clock |-> c]
AckMessage == [type |-> "ack", clock |-> 0]
RelMessage == [type |-> "rel", clock |-> 0]

SeqOf(S, n) == UNION {[1..m -> S] : m \in 0..n}
BoundedSeq(S, n) == SeqOf(S, n)

Message == {AckMessage, RelMessage} \union {ReqMessage(c) : c \in Clock}

(***************************************************************************)
(* The type correctness predicate.                                         *)
(***************************************************************************)  
TypeOK ==
     (* clock[p] is the local clock of process p *)
  /\ clock \in [Proc -> Clock]
     (* req[p][q] stores the clock associated with request from q received by p, 0 if none *)
  /\ req \in [Proc -> [Proc -> Nats]]
     (* ack[p] stores the processes that have ack'ed p's request *)
  /\ ack \in [Proc -> SUBSET Proc]
     (* network[p][q]: queue of messages from p to q -- pairwise FIFO communication *)
  /\ network \in [Proc -> [Proc -> Seq(Message)]]
     (* set of processes in critical section: should be empty or singleton *)
  /\ crit \in SUBSET Proc

TypeOKRandom ==
     (* clock[p] is the local clock of process p *)
  /\ clock \in [Proc -> Clock]
     (* req[p][q] stores the clock associated with request from q received by p, 0 if none *)
  /\ req \in [Proc -> [Proc -> Nats]]
     (* ack[p] stores the processes that have ack'ed p's request *)
  /\ ack \in [Proc -> SUBSET Proc]
     (* network[p][q]: queue of messages from p to q -- pairwise FIFO communication *)
  /\ network \in [Proc -> [Proc -> RandomSubset(4, BoundedSeq(Message, 2))]]
     (* set of processes in critical section: should be empty or singleton *)
  /\ crit \in SUBSET Proc


(***************************************************************************)
(* The initial state predicate.                                            *)
(***************************************************************************) 
Init ==
  /\ clock = [p \in Proc |-> 1]
  /\ req = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ ack = [p \in Proc |-> {}]
  /\ network = [p \in Proc |-> [q \in Proc |-> <<>> ]]
  /\ crit = {}

(***************************************************************************)
(* beats(p,q) is true if process p believes that its request has higher    *)
(* priority than q's request. This is true if either p has not received a  *)
(* request from q or p's request has a smaller clock value than q's.       *)
(* If there is a tie, the numerical process ID decides.                    *)
(***************************************************************************)
beats(p,q) ==
  \/ req[p][q] = 0
  \/ req[p][p] < req[p][q]
  \/ req[p][p] = req[p][q] /\ p < q
  
(***************************************************************************)
(* Broadcast a message: send it to all processes except the sender.        *)
(***************************************************************************)
Broadcast(s, m) ==
  [r \in Proc |-> IF s=r THEN network[s][r] ELSE Append(network[s][r], m)]

(***************************************************************************)
(* Process p requests access to critical section.                          *)
(***************************************************************************)
Request(p) ==
  /\ req[p][p] = 0
  /\ req'= [req EXCEPT ![p][p] = clock[p]]
  /\ network' = [network EXCEPT ![p] = Broadcast(p, ReqMessage(clock[p]))]
  /\ ack' = [ack EXCEPT ![p] = {p}]
  /\ UNCHANGED <<clock, crit>>

(***************************************************************************)
(* Process p receives a request from q and acknowledges it.                *)
(***************************************************************************)
ReceiveRequest(p,q) ==
  /\ network[q][p] # << >>
  /\ LET m == Head(network[q][p])
         c == m.clock
     IN  /\ m.type = "req"
         /\ req' = [req EXCEPT ![p][q] = c]
         /\ clock' = [clock EXCEPT ![p] = IF c > clock[p] THEN c + 1 ELSE @ + 1]
         /\ network' = [network EXCEPT ![q][p] = Tail(@),
                                       ![p][q] = Append(@, AckMessage)]
         /\ UNCHANGED <<ack, crit>>

(***************************************************************************)
(* Process p receives an acknowledgement from q.                           *)
(***************************************************************************)      
ReceiveAck(p,q) ==
  /\ network[q][p] # << >>
  /\ LET m == Head(network[q][p])
     IN  /\ m.type = "ack"
         /\ ack' = [ack EXCEPT ![p] = @ \union {q}]
         /\ network' = [network EXCEPT ![q][p] = Tail(@)]
         /\ UNCHANGED <<clock, req, crit>>

(**************************************************************************)
(* Process p enters the critical section.                                 *)
(**************************************************************************)
Enter(p) == 
  /\ ack[p] = Proc
  /\ \A q \in Proc \ {p} : beats(p,q)
  /\ crit' = crit \union {p}
  /\ UNCHANGED <<clock, req, ack, network>>
  
(***************************************************************************)
(* Process p exits the critical section and notifies other processes.      *)
(***************************************************************************)
Exit(p) ==
  /\ p \in crit
  /\ crit' = crit \ {p}
  /\ network' = [network EXCEPT ![p] = Broadcast(p, RelMessage)]
  /\ req' = [req EXCEPT ![p][p] = 0]
  /\ ack' = [ack EXCEPT ![p] = {}]
  /\ UNCHANGED clock
 
(***************************************************************************)
(* Process p receives a release notification from q.                       *)
(***************************************************************************)
ReceiveRelease(p,q) ==
  /\ network[q][p] # << >>
  /\ LET m == Head(network[q][p])
     IN  /\ m.type = "rel"
         /\ req' = [req EXCEPT ![p][q] = 0]
         /\ network' = [network EXCEPT ![q][p] = Tail(@)]
         /\ UNCHANGED <<clock, ack, crit>>

(***************************************************************************)
(* Next-state relation.                                                    *)
(***************************************************************************)

RequestAction == TRUE /\ \E p \in Proc : Request(p) 
EnterAction == TRUE /\ \E p \in Proc : Enter(p)
ExitAction == TRUE /\ \E p \in Proc : Exit(p)
ReceiveRequestAction == TRUE /\ \E p \in Proc : \E q \in Proc \ {p} : ReceiveRequest(p,q)
ReceiveAckAction == TRUE /\ \E p \in Proc : \E q \in Proc \ {p} : ReceiveAck(p,q)
ReceiveReleaseAction == TRUE /\ \E p \in Proc : \E q \in Proc \ {p} : ReceiveRelease(p,q)

Next ==
    \/ RequestAction
    \/ EnterAction
    \/ ExitAction
    \/ ReceiveRequestAction
    \/ ReceiveAckAction
    \/ ReceiveReleaseAction


vars == <<req, network, clock, ack, crit>>

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* A state constraint that is useful for validating the specification      *)
(* using finite-state model checking.                                      *)
(***************************************************************************)
ClockConstraint == \A p \in Proc : clock[p] <= maxClock

(***************************************************************************)
(* No channel ever contains more than three messages. In fact, no channel  *)
(* ever contains more than one message of the same type, as proved below.  *)
(***************************************************************************)
BoundedNetwork == \A p,q \in Proc : Len(network[p][q]) <= 3

(***************************************************************************)
(* The main safety property of mutual exclusion.                           *)
(***************************************************************************)
Mutex == \A p,q \in crit : p = q

CTICost == 0
NextUnchanged == UNCHANGED vars

Contains(s,mtype) == \E i \in 1 .. Len(s) : s[i].type = mtype
Count(s,mt) == Cardinality({i \in 1 .. Len(s) : s[i].type = mt})
Precedes(s,mt1,mt2) == \A i,j \in 1 .. Len(s) : s[i].type = mt1 /\ s[j].type = mt2 => i < j

LInv5091_971a_R0_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : (ack[VARI] = {}) \/ (~(VARJ \in crit) \/ (~(beats(VARI,VARJ) /\ req = req)))

H_Inv36_R0_0_I1_def == \A VARI \in Proc : \A VARJ \in Proc : (VARI # VARJ /\ ack = ack) \/ (~(network[VARI][VARJ] # <<>>))
H_Inv306_R1_0_I1_def == \A VARI \in Proc : (ack[VARI] = Proc) \/ (~(VARI \in crit))
H_Inv875_R2_0_I1_def == \A VARI \in Proc : \A VARJ \in Proc : ~(VARJ \in crit) \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
H_Inv840_R3_0_I1_def == \A VARI \in Proc : \A VARJ \in Proc : ~(VARI \in ack[VARJ]) \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
H_Inv695_R3_0_I1_def == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(VARI \in ack[VARJ]))
H_Inv381_R4_0_I1_def == \A VARI \in Proc : \A VARJ \in Proc : (beats(VARI,VARJ)) \/ (~(ack[VARI] = {}))
H_Inv92_R5_0_I1_def == \A VARI \in Proc : (VARI \in ack[VARI]) \/ ((ack[VARI] = {}))

HInv19_R0_0_I1 == \A VARI \in Proc : ~(VARI \in crit)

H_Inv565 == \A VARI \in Proc : \A VARJ \in Proc : ~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "ack") \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))

LInv6058_971a_R0_0_I2 == 
    \A VARI \in Proc : 
    \A VARJ \in Proc : 
        (ack[VARI] = {}) \/ (~(VARJ \in crit) \/ (~(beats(VARI,VARJ) /\ req = req)))

LInv5855_236a == 
    \A VARI \in Proc : 
    \A VARJ \in Proc : 
      (ack[VARI] = {}) \/ (~(VARJ \in crit)) \/ (~(beats(VARI,VARJ) /\ req = req))


A_Inv364_R0_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(VARI \in ack[VARJ]) \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
A_Inv186_R0_0_I1 == \A VARI \in Proc : (ack[VARI] = Proc) \/ (~(VARI \in crit))
A_Inv275_R0_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(VARI \in ack[VARJ]))
A_Inv165_R0_0_I1 == \A VARI \in Proc : (\A VOTHER \in Proc \ {VARI} : beats(VARI,VOTHER) /\ req = req) \/ (~(VARI \in crit))
A_Inv1320_R1_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "ack") \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
A_Inv39_R1_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : (VARI # VARJ /\ ack = ack) \/ (~(network[VARI][VARJ] # <<>>))
A_Inv914_R3_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (req[VARI][VARI] = network[VARI][VARJ][VARRINDI].clock) \/ (~(network[VARI][VARJ][VARRINDI].type = "req"))
A_Inv166_R4_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(VARJ \in crit))
A_Inv35_R7_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (VARI # VARJ /\ crit = crit) \/ (~(network[VARI][VARJ] # <<>>))

IndGlobal1 == 
  /\ Mutex
  /\ A_Inv364_R0_0_I1
  /\ A_Inv1320_R1_0_I1
  /\ A_Inv914_R3_1_I1
  /\ A_Inv35_R7_0_I1
  /\ A_Inv39_R1_1_I1
  /\ A_Inv186_R0_0_I1
  /\ A_Inv275_R0_0_I1
  /\ A_Inv165_R0_0_I1
  /\ A_Inv166_R4_1_I1

B_Inv364_R0_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(VARI \in ack[VARJ]) \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
B_Inv186_R0_0_I1 == \A VARI \in Proc : (ack[VARI] = Proc) \/ (~(VARI \in crit))
B_Inv275_R0_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(VARI \in ack[VARJ]))
B_Inv229_R0_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (beats(VARI,VARJ) /\ req = req) \/ (~(ack[VARI] = {}))
B_Inv1320_R1_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "ack") \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
B_Inv914_R1_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (req[VARI][VARI] = network[VARI][VARJ][VARRINDI].clock) \/ (~(network[VARI][VARJ][VARRINDI].type = "req"))
B_Inv39_R3_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : (VARI # VARJ /\ ack = ack) \/ (~(network[VARI][VARJ] # <<>>))
B_Inv839_R5_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "rel") \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
B_Inv549_R6_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (network[VARI][VARJ][VARRINDI].type = "ack") \/ (~(VARI \in crit))
B_Inv1330_R9_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(VARJ \in crit))

IndGlobal2 == 
    /\ B_Inv364_R0_0_I1
    /\ B_Inv186_R0_0_I1
    /\ B_Inv275_R0_0_I1
    /\ B_Inv229_R0_0_I1
    /\ B_Inv1320_R1_0_I1
    /\ B_Inv914_R1_1_I1
    /\ B_Inv39_R3_1_I1
    /\ B_Inv839_R5_1_I1
    /\ B_Inv549_R6_0_I1
    /\ B_Inv1330_R9_1_I1

LInv395_3bd9_R3_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Count(network[VARI][VARJ], "req") > 0) \/ (~(ack[VARI] = {}))


P_Inv1250_R0_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "ack"))
P_Inv124_R0_1_I1 == \A VARI \in Proc : (VARI \in ack[VARI]) \/ ((ack[VARI] = {}))
P_Inv35_R1_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (VARI # VARJ /\ crit = crit) \/ (~(network[VARI][VARJ] # <<>>))
P_Inv574_R1_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (req[VARI][VARI] = network[VARI][VARJ][VARRINDI].clock) \/ (~(network[VARI][VARJ][VARRINDI].type = "req"))
P_Inv832_R1_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "rel") \/ (~(network[VARJ][VARI] # <<>> /\ req[VARI][VARJ] > Head(network[VARJ][VARI]).clock))
P_Inv553_R1_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : (network[VARJ][VARI] # <<>>) \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
P_Inv653_R1_2_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (req[VARI][VARJ] > 0) \/ (~(network[VARI][VARJ][VARRINDI].type = "ack"))
P_Inv19_R2_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (VARI # VARJ /\ ack = ack) \/ (~(network[VARI][VARJ] # <<>>))
P_Inv282_R2_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : ~(ack[VARI] = {}) \/ (~(network[VARI][VARJ][VARRINDI].type = "req"))
P_Inv259_R2_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(VARI \in ack[VARJ]) \/ (~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "ack"))
P_Inv549_R4_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (network[VARI][VARJ][VARRINDI].type = "ack") \/ (~(VARI \in crit))
P_Inv938_R5_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : ~(network[VARI][VARJ][VARRINDI].type = "rel") \/ (~(network[VARJ][VARI] # <<>> /\ req[VARI][VARJ] > Head(network[VARJ][VARI]).clock))
P_Inv582_R6_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (req[VARI][VARI] = network[VARI][VARJ][VARRINDI].clock) \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
P_Inv912_R6_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(network[VARI][VARJ] # <<>>) \/ (~(network[VARJ][VARI] # <<>> /\ req[VARI][VARJ] = Head(network[VARJ][VARI]).clock))
P_Inv263_R10_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : ~(VARI \in ack[VARJ]) \/ (~(network[VARI][VARJ][VARRINDI].type = "ack"))
P_Inv270_R15_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(ack[VARI] = Proc) \/ (~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "req"))
P_Inv2170_R16_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : ~(VARI \in ack[VARJ]) \/ (~(network[VARJ][VARI] # <<>>)) \/ (~(network[VARI][VARJ] # <<>>))
P_Inv289_R16_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (VARI \in ack[VARI]) \/ ((ack[VARI] = Proc) \/ (~(network[VARI][VARJ][VARRINDI].type = "req")))
P_Inv179_R17_0_I1 == \A VARI \in Proc : (ack[VARI] = Proc) \/ (~(VARI \in crit))
P_Inv277_R19_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(VARJ \in crit))
P_Inv275_R20_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(VARI \in ack[VARJ]))




LInv9213_b6f0_R0_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : (ack[VARI] = {}) \/ (~(beats(VARI,VARJ) /\ req = req)) \/ (~(VARJ \in crit))
LInv6102_604b_R1_0_I3 == \A VARI \in Proc : \A VARJ \in Proc : (ack[VARI] = {}) \/ (~(beats(VARI,VARJ) /\ req = req) \/ (~(beats(VARJ,VARI) /\ req = req))) \/ (~(VARI \in ack[VARJ]))
LInv3265_fc6b_R1_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARJ][VARI], "ack")) \/ (~(ack[VARI] = {}))
LInv793_7d37_R1_2_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARI][VARJ], "rel")) \/ (~(VARI \in crit))
LInv253_245d_R1_3_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARI][VARJ], "req")) \/ (~(VARI \in crit))
LInv24_d50f_R1_4_I2 == \A VARI \in Proc : \A VARJ \in Proc : (VARI # VARJ /\ ack = ack) \/ ((ack[VARI] = Proc)) \/ (~(VARI \in crit))
LInv2105_1d4d_R1_4_I2 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] = 0) \/ (~(beats(VARJ,VARI) /\ req = req)) \/ (~(VARI \in crit))
LInv959_fd4e_R1_4_I2 == \A VARI \in Proc : \A VARJ \in Proc : (clock[VARJ] > req[VARI][VARI]) \/ (~(VARI # VARJ /\ req = req)) \/ (~(VARJ \in ack[VARI]))
LInv1378_911a_R1_4_I2 == \A VARI \in Proc : \A VARJ \in Proc : (ack[VARI] = Proc) \/ (~(req[VARI][VARJ] > req[VARJ][VARJ])) \/ (~(VARJ \in crit))
LInv982_e47b_R1_4_I2 == \A VARI \in Proc : \A VARJ \in Proc : ~(VARJ \in crit) \/ (~(req[VARI][VARJ] = 0)) \/ (~(ack[VARI] = {}))
LInv6731_07b2_R2_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (network[VARI][VARJ][VARRINDI].type = "ack") \/ (~(Precedes(network[VARI][VARJ], "req", "rel"))) \/ ((req[VARI][VARI] = network[VARI][VARJ][VARRINDI].clock))
LInv2559_1d23_R2_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (req[VARI][VARI] = 0) \/ (~(VARJ \in ack[VARI])) \/ ((req[VARJ][VARI] > network[VARI][VARJ][VARRINDI].clock))
LInv1587_cca9_R2_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (ack[VARI] = Proc) \/ ((network[VARI][VARJ][VARRINDI].type = "req") \/ (~(req[VARI][VARJ] > req[VARJ][VARJ])))
LInv1056_c1cf_R2_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : (VARI # VARJ /\ ack = ack) \/ ((VARI < VARJ /\ ack = ack) \/ (~(network[VARI][VARI] # <<>>)))
LInv2863_1472_R2_1_I2 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (network[VARI][VARJ][VARRINDI].clock = req[VARI][VARI]) \/ ((network[VARI][VARJ][VARRINDI].type = "rel") \/ (~(network[VARI][VARJ][VARRINDI].type = "req")))
LInv3989_c40b_R2_1_I2 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARJ][VARI], "rel")) \/ (~(req[VARI][VARI] > 0)) \/ (~(VARI \in ack[VARJ]))
LInv1017_db44_R2_2_I2 == \A VARI \in Proc : \A VARJ \in Proc : (beats(VARJ,VARI) /\ req = req) \/ (~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "req")) \/ (~(network[VARI][VARJ] # <<>>))
LInv71_dd88_R2_3_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(VARI \in ack[VARJ]) \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
LInv65_6f6e_R2_3_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(VARI \in ack[VARJ]))
LInv458_765c_R3_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARI][VARJ], "ack")) \/ (~(VARJ \in crit))
LInv119_d6ca_R3_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARI][VARJ], "req")) \/ (~(ack[VARI] = {}))
LInv710_2621_R4_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARI][VARJ], "rel")) \/ (~(ack[VARI] = Proc))
LInv666_2954_R5_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARI][VARJ], "req")) \/ (~(ack[VARI] = Proc))
LInv1332_12c5_R5_1_I1 == \A VARI \in Proc : (req[VARI][VARI] > 0) \/ (~(VARI \in crit))
LInv40_8f4b_R6_0_I1 == \A VARI \in Proc : (ack[VARI] = {}) \/ ((req[VARI][VARI] > 0))
LInv883_d48e_R7_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : (ack[VARI] = {}) \/ (~(beats(VARI,VARJ) /\ req = req) \/ (~(req[VARI][VARJ] > req[VARJ][VARJ])))
LInv51_02b8_R7_0_I2 == \A VARI \in Proc : (req[VARI][VARI] = 0) \/ (~(ack[VARI] = {}))
LInv2417_7c41_R7_3_I2 == \A VARI \in Proc : \A VARJ \in Proc : (VARI \in crit) \/ ((req[VARI][VARJ] = 0) \/ (~(network[VARI][VARI] # <<>>)))
LInv6_7683_R8_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (clock[VARJ] > req[VARI][VARI]) \/ (~(Contains(network[VARJ][VARI], "ack")))
LInv3_4882_R11_1_I0 == \A VARI \in Proc : \A VARJ \in Proc : (\A mi \in 1 .. Len(network[VARI][VARJ]) : network[VARI][VARJ][mi].type = "req" => network[VARI][VARJ][mi].clock = req[VARI][VARI])
LInv8_c48d_R11_2_I0 == \A VARI \in Proc : ~(network[VARI][VARI] # <<>>)
LInv590_66ff_R12_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (req[VARJ][VARI] > network[VARI][VARJ][VARRINDI].clock) \/ (~(Contains(network[VARJ][VARI], "ack")))
LInv494_a3d0_R12_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARI][VARJ], "rel")) \/ (~(VARJ \in ack[VARI]))
LInv6704_0d1f_R12_2_I2 == \A VARI \in Proc : \A VARJ \in Proc : \A VARK \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (req[VARI][VARJ] > req[VARI][VARK]) \/ (~(req[VARJ][VARI] > network[VARI][VARJ][VARRINDI].clock)) \/ (~(network[VARI][VARJ][VARRINDI].type = "req"))
LInv8263_d9cd_R13_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : \A VARK \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (network[VARI][VARJ][VARRINDI].type = "ack") \/ ((req[VARI][VARJ] > req[VARI][VARK]) \/ (~(VARI \in crit)))
LInv5324_c7ac_R13_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : (VARJ \in crit) \/ (~(VARI # VARJ /\ crit = crit)) \/ (~(VARI \in crit))
LInv25_af7e_R13_1_I0 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : ~(network[VARI][VARJ][VARRINDI].clock > req[VARI][VARI])
LInv604_98d1_R16_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARI][VARJ], "ack")) \/ (~(Contains(network[VARJ][VARI], "rel")))
LInv686_a109_R16_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (network[VARI][VARJ][VARRINDI].type = "ack") \/ (~(VARJ \in ack[VARI]))
LInv2092_2de5_R17_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : (beats(VARJ,VARI) /\ req = req) \/ (~(Precedes(network[VARI][VARJ], "req", "rel"))) \/ (~(Contains(network[VARI][VARJ], "req")))
LInv2_3687_R17_1_I0 == \A VARI \in Proc : \A VARJ \in Proc : (Count(network[VARI][VARJ], "req") <= 1)
LInv4529_96d0_R17_2_I2 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (req[VARI][VARI] > req[VARI][VARJ]) \/ (~(network[VARJ][VARI] # <<>>)) \/ ((req[VARJ][VARI] > network[VARI][VARJ][VARRINDI].clock))
LInv551_515e_R17_2_I2 == \A VARI \in Proc : \A VARJ \in Proc : (Contains(network[VARI][VARJ], "req")) \/ (~(VARI # VARJ /\ clock = clock)) \/ ((clock[VARJ] > req[VARI][VARI]))
LInv5657_a105_R17_2_I2 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (req[VARI][VARI] = network[VARI][VARJ][VARRINDI].clock) \/ (~(req[VARI][VARJ] > req[VARJ][VARJ])) \/ (~(VARI # VARJ /\ network = network))

==============================================================================
==============================================================================
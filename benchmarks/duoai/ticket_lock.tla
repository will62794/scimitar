--------------------------- MODULE ticket_lock ---------------------------

EXTENDS Naturals, FiniteSets

(***************************************************************************)
(* Constants and basic order on tickets                                    *)
(***************************************************************************)

CONSTANTS
  THREAD,
  TICKET,
  zero,
  le        \* subset of TICKET × TICKET

Le(x, y) == <<x, y>> \in le

ASSUME
  /\ zero \in TICKET
  /\ le \subseteq TICKET \X TICKET

  /\ \A x \in TICKET : Le(x, x)                             \* reflexive
  /\ \A x, y, z \in TICKET :
        (Le(x, y) /\ Le(y, z)) => Le(x, z)                 \* transitive
  /\ \A x, y \in TICKET :
        (Le(x, y) /\ Le(y, x)) => x = y                    \* antisym
  /\ \A x, y \in TICKET :
        Le(x, y) \/ Le(y, x)                               \* total
  /\ \A x \in TICKET : Le(zero, x)                         \* zero is minimal

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)

VARIABLES
  pc1, pc2, pc3,      \* subsets of THREAD: program counters
  service,            \* current service ticket
  next_ticket,        \* next available ticket
  m                   \* THREAD × TICKET mapping (relation form)

Vars == <<pc1, pc2, pc3, service, next_ticket, m>>

Pc1(t) == t \in pc1
Pc2(t) == t \in pc2
Pc3(t) == t \in pc3
M(t, k) == <<t, k>> \in m

TypeInv ==
  /\ pc1 \subseteq THREAD
  /\ pc2 \subseteq THREAD
  /\ pc3 \subseteq THREAD
  /\ service \in TICKET
  /\ next_ticket \in TICKET
  /\ m \subseteq THREAD \X TICKET

(* helper: override all pairs whose first component is t with new second-set S *)
OverrideRow(R, t, S) ==
  { r \in R : r[1] # t }
  \cup { <<t, k>> : k \in S }

(***************************************************************************)
(* Init                                                                    *)
(***************************************************************************)

Init ==
  /\ pc1 = THREAD
  /\ pc2 = {}
  /\ pc3 = {}
  /\ service = zero
  /\ next_ticket = zero
  /\ m = { <<t, zero>> : t \in THREAD }

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

(* step12(t, new_next_ticket) *)
Step12(t, new_next_ticket) ==
  /\ t \in THREAD /\ new_next_ticket \in TICKET
  /\ Pc1(t)

  /\ ~Le(new_next_ticket, next_ticket)
  /\ \A Z \in TICKET :
        (~Le(Z, next_ticket)) => Le(new_next_ticket, Z)

  /\ pc1' = pc1 \ {t}
  /\ pc2' = pc2 \cup {t}
  /\ pc3' = pc3

  /\ m' = OverrideRow(m, t, {next_ticket})

  /\ next_ticket' = new_next_ticket
  /\ service' = service

(* step23(t, k) *)
Step23(t, k) ==
  /\ t \in THREAD /\ k \in TICKET
  /\ Pc2(t)
  /\ M(t, k)
  /\ Le(k, service)

  /\ pc2' = pc2 \ {t}
  /\ pc3' = pc3 \cup {t}
  /\ pc1' = pc1

  /\ m' = m
  /\ service' = service
  /\ next_ticket' = next_ticket

(* step31(t, new_service) *)
Step31(t, new_service) ==
  /\ t \in THREAD /\ new_service \in TICKET
  /\ Pc3(t)

  /\ ~Le(new_service, service)
  /\ \A Z \in TICKET :
        (~Le(Z, service)) => Le(new_service, Z)

  /\ service' = new_service

  /\ pc3' = pc3 \ {t}
  /\ pc1' = pc1 \cup {t}
  /\ pc2' = pc2

  /\ m' = m
  /\ next_ticket' = next_ticket

(***************************************************************************)
(* Next and Spec                                                           *)
(***************************************************************************)

Next ==
  \/ \E t \in THREAD, nt \in TICKET : Step12(t, nt)
  \/ \E t \in THREAD, k  \in TICKET : Step23(t, k)
  \/ \E t \in THREAD, ns \in TICKET : Step31(t, ns)
  \/ UNCHANGED Vars

Spec == Init /\ [][Next]_Vars /\ []TypeInv

(***************************************************************************)
(* Safety: at most one thread in pc3                                       *)
(***************************************************************************)

MutualExcl ==
  \A T1, T2 \in THREAD :
    (Pc3(T1) /\ Pc3(T2)) => T1 = T2

THEOREM Spec => []MutualExcl

=============================================================================
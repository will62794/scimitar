--------------------------- MODULE ticket_lock ---------------------------

EXTENDS Naturals, FiniteSets

(***************************************************************************)
(* Constants and basic order on tickets                                    *)
(***************************************************************************)

CONSTANTS
  Thread,
  Ticket,
  zero

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)

VARIABLES
  pc,      \* program counters
  service,            \* current service ticket
  next_ticket,        \* next available ticket
  m                   \* THREAD × TICKET mapping (relation form)

Vars == <<pc, service, next_ticket, m>>

M(t, k) == <<t, k>> \in m

(***************************************************************************)
(* Init                                                                    *)
(***************************************************************************)

Init ==
  /\ pc = [t \in Thread |-> "pc1"]
  /\ service = zero
  /\ next_ticket = zero
  /\ m = { <<t, zero>> : t \in Thread }

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

(* step12(t, new_next_ticket) *)
Step12(t, new_next_ticket) ==
  /\ pc[t] = "pc1"
  /\ ~(new_next_ticket <= next_ticket)
  /\ \A Z \in Ticket : (~(Z <= next_ticket)) => (new_next_ticket <= Z)
  /\ pc' = [pc EXCEPT ![t] = "pc2"]
  /\ m' = (m \ {<<t,notk>> : notk \in Ticket \ {next_ticket}}) \cup {<<t,next_ticket>>}
  /\ next_ticket' = new_next_ticket
  /\ service' = service

(* step23(t, k) *)
Step23(t, k) ==
  /\ pc[t] = "pc2"
  /\ <<t, k>> \in m
  /\ (k <= service)
  /\ pc' = [pc EXCEPT ![t] = "pc3"]
  /\ m' = m
  /\ service' = service
  /\ next_ticket' = next_ticket

(* step31(t, new_service) *)
Step31(t, new_service) ==
  /\ pc[t] = "pc3"
  /\ ~(new_service <= service)
  /\ \A Z \in Ticket : (~(Z <= service)) => (new_service <= Z)
  /\ service' = new_service
  /\ pc' = [pc EXCEPT ![t] = "pc1"]
  /\ m' = m
  /\ next_ticket' = next_ticket

(***************************************************************************)
(* Next and Spec                                                           *)
(***************************************************************************)

Step12Action == TRUE /\ \E t \in Thread, nt \in Ticket : Step12(t, nt)
Step23Action == TRUE /\ \E t \in Thread, k  \in Ticket : Step23(t, k)
Step31Action == TRUE /\ \E t \in Thread, ns \in Ticket : Step31(t, ns)

Next ==
  \/ Step12Action
  \/ Step23Action
  \/ Step31Action


TypeOK ==
  /\ pc \in [Thread -> {"pc1", "pc2", "pc3"}]
  /\ service \in Ticket
  /\ next_ticket \in Ticket
  /\ m \subseteq Thread \X Ticket

(***************************************************************************)
(* Safety: at most one thread in pc3                                       *)
(***************************************************************************)

MutualExcl ==
  \A T1, T2 \in Thread :
    (pc[T1] = "pc3" /\ pc[T2] = "pc3") => T1 = T2

CTICost == 0

=============================================================================
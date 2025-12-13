--------------------------- MODULE distributed_lock ---------------------------
(***************************************************************************)
(* TLA+ specification of the distributed lock protocol                    *)
(* Converted from Ivy specification                                        *)
(* Original source: https://github.com/Microsoft/Ironclad/blob/master/    *)
(*                 ironfleet/src/Dafny/Distributed/Protocol/Lock/Node.i.dfy *)
(*                                                                         *)
(* For a description of the protocol, see the IronFleet paper             *)
(* (https://www.microsoft.com/en-us/research/wp-content/uploads/2015/10/ *)
(*  ironfleet.pdf), Figure 4                                              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

(***************************************************************************)
(* Constants                                                                *)
(***************************************************************************)
CONSTANTS Node, \* Set of nodes
          Epoch \* Set of epochs

\* ASSUME First \in Node
\* ASSUME E1 \in Nat /\ E1 > 0

(***************************************************************************)
(* Variables                                                                *)
(***************************************************************************)
VARIABLES ep, \* ep[n] is the current epoch of node n
          held, \* held[n] is true iff the lock is currently held by node n
          transfer, \* Set of transfer messages: {[epoch |-> e, dest |-> n] : ...}
          locked, \* Set of locked messages: {[epoch |-> e, source |-> n] : ...}
          first,
          e1
(***************************************************************************)
(* Type correctness predicate                                               *)
(***************************************************************************)
TypeOK ==
    /\ first \in Node
    /\ ep \in [Node -> Nat]
    /\ held \in [Node -> BOOLEAN]
    /\ transfer \in SUBSET ({[epoch |-> e, dest |-> n] : e \in Nat, n \in Node})
    /\ locked \in SUBSET ({[epoch |-> e, source |-> n] : e \in Nat, n \in Node})

(***************************************************************************)
(* Initial state predicate                                                 *)
(***************************************************************************)
Init ==
    /\ first \in Node
    /\ e1 \in Epoch /\ e1 # 0
    /\ held = [n \in Node |-> (n = first)]
    /\ ep = [n \in Node |-> IF n = first THEN e1 ELSE 0]
    /\ transfer = {}
    /\ locked = {}

(***************************************************************************)
(* Action: grant(n1, n2, e)                                                *)
(* Release the lock and send a transfer message                            *)
(***************************************************************************)
Grant(n1, n2, e) ==
    /\ held[n1]
    /\ ~(e <= ep[n1])  \* jump to some strictly higher epoch
    /\ transfer' = transfer \union {[epoch |-> e, dest |-> n2]}
    /\ held' = [held EXCEPT ![n1] = FALSE]
    /\ UNCHANGED <<ep, locked, first, e1>>

(***************************************************************************)
(* Action: accept(n, e)                                                    *)
(* Receive a transfer message and take the lock, sending a locked message  *)
(***************************************************************************)
Accept(n, e) ==
    /\ [epoch |-> e, dest |-> n] \in transfer
    /\ IF ~(e <= ep[n])
       THEN /\ held' = [held EXCEPT ![n] = TRUE]
            /\ ep' = [ep EXCEPT ![n] = e]
            /\ locked' = locked \union {[epoch |-> e, source |-> n]}
       ELSE /\ UNCHANGED <<held, ep, locked>>
    /\ transfer' = transfer \* \ {[epoch |-> e, dest |-> n]}
    /\ UNCHANGED <<first, e1>>

(***************************************************************************)
(* Next-state relation                                                     *)
(***************************************************************************)
Next ==
    \/ \E n1, n2 \in Node, e \in Epoch : Grant(n1, n2, e)
    \/ \E n \in Node, e \in Epoch : Accept(n, e)

vars == <<ep, held, transfer, locked>>

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety property: at most one node can have locked a given epoch        *)
(***************************************************************************)
LockInv ==
    \A e \in Epoch, n1, n2 \in Node :
        [epoch |-> e, source |-> n1] \in locked /\
        [epoch |-> e, source |-> n2] \in locked
        => (n1 = n2)

=============================================================================


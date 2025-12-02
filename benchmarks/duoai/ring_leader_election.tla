---- MODULE ring_leader_election ----
EXTENDS TLC


\* type node
\* type id
CONSTANT node
CONSTANT id

\* # A ring topology of nodes
\* instantiate ring : ring_topology(node)

\* # A total order on ids
\* relation le(X:id, Y:id)
\* instantiate total_order(le)

\* # A function relating a node to its id
\* function idn(X:node) : id
\* axiom idn(X) = idn(Y) -> X = Y  # the idn function is injective

\* # A relation that keeps track of nodes that think they are the leader
\* relation leader(N:node)

\* # A relation for pending messages, a message is just an id
\* relation pending(V:id, N:node) # The identity V is pending at node N

VARIABLE leader
VARIABLE pending

\* after init {
\*     leader(N) := false;
\*     pending(V,N) := false;
\* }

\* action send(n: node, n1: node) = {
\*     # send my own id to the next node
\*     require n ~= n1 & ((Z ~= n & Z ~= n1) -> ring.btw(n, n1, Z));
\*     pending(idn(n), n1) := true;
\* }

\* action become_leader(n: node) = {
\*     require pending(idn(n), n);
\*     leader(n) := true;
\* }

\* action receive(n: node, m: id, n1: node) = {
\*     require pending(m, n);
\*     require n ~= n1 & ((Z ~= n & Z ~= n1) -> ring.btw(n, n1, Z));
\* #    require m ~= idn(n);
\*     if le(idn(n), m) {
\*         pending(m, n1) := true;
\*     };
\* }

Vars == <<leader, pending>>

(***************************************************************************)
(* Init                                                                    *)
(***************************************************************************)

Init ==
  /\ leader \in [node -> BOOLEAN]
  /\ pending \in [id -> [node -> BOOLEAN]]
  /\ \A n \in node : leader[n] = FALSE
  /\ \A v \in id : \A n \in node : pending[v][n] = FALSE

(***************************************************************************)
(* Helper: idn is a function from node to id, injective                    *)
(***************************************************************************)

ASSUME idn \in [node -> id]
ASSUME \A x, y \in node : idn[x] = idn[y] => x = y

(***************************************************************************)
(* The ring.btw relation on the node set                                   *)
(***************************************************************************)

ASSUME ring_btw \in [node -> [node -> [node -> BOOLEAN]]]
(* Properties of ring_btw are assumed elsewhere *)

(***************************************************************************)
(* The le relation: a total order on ids                                   *)
(***************************************************************************)

ASSUME le \in [id -> [id -> BOOLEAN]]
(* le is a total order *)

(***************************************************************************)
(* Action: Send                                                            *)
(***************************************************************************)

Send(n, n1) ==
  /\ n \in node
  /\ n1 \in node
  /\ n # n1
  /\ \A Z \in node : (Z # n /\ Z # n1) => ring_btw[n][n1][Z]
  /\ pending' = [pending EXCEPT ![idn[n]][n1] = TRUE]
  /\ UNCHANGED leader

(***************************************************************************)
(* Action: BecomeLeader                                                    *)
(***************************************************************************)

BecomeLeader(n) ==
  /\ n \in node
  /\ pending[idn[n]][n]
  /\ leader' = [leader EXCEPT ![n] = TRUE]
  /\ UNCHANGED pending

(***************************************************************************)
(* Action: Receive                                                         *)
(***************************************************************************)

Receive(n, m, n1) ==
  /\ n \in node
  /\ m \in id
  /\ n1 \in node
  /\ pending[m][n]
  /\ n # n1
  /\ \A Z \in node : (Z # n /\ Z # n1) => ring_btw[n][n1][Z]
  /\ IF le[idn[n]][m]
        THEN pending' = [pending EXCEPT ![m][n1] = TRUE]
        ELSE pending' = pending
  /\ UNCHANGED leader

(***************************************************************************)
(* Next operator                                                           *)
(***************************************************************************)

Next ==
  \E n \in node : \E n1 \in node : Send(n, n1)
  \/ \E n \in node : BecomeLeader(n)
  \/ \E n \in node : \E m \in id : \E n1 \in node : Receive(n, m, n1)





====
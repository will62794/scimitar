---- MODULE ring_leader_election ----
EXTENDS TLC, Naturals, FiniteSets

CONSTANT Node
CONSTANT Id

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
VARIABLE idn

Vars == <<leader, pending>>

Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y

(***************************************************************************)
(* Init                                                                    *)
(***************************************************************************)

Init ==
  /\ leader \in [Node -> BOOLEAN]
  /\ pending \in [Id -> [Node -> BOOLEAN]]
  /\ \A n \in Node : leader[n] = FALSE
  /\ \A v \in Id : \A n \in Node : pending[v][n] = FALSE
  /\ idn \in [Node -> Id]
  /\ Injective(idn)

(***************************************************************************)
(* Helper: idn is a function from node to id, injective                    *)
(***************************************************************************)

\* ASSUME idn \in [node -> id]
\* ASSUME \A x, y \in node : idn[x] = idn[y] => x = y

\* (***************************************************************************)
\* (* The ring.btw relation on the node set                                   *)
\* (***************************************************************************)

\* ASSUME ring_btw \in [node -> [node -> [node -> BOOLEAN]]]
\* (* Properties of ring_btw are assumed elsewhere *)

\* (***************************************************************************)
\* (* The le relation: a total order on ids                                   *)
\* (***************************************************************************)

\* ASSUME le \in [id -> [id -> BOOLEAN]]
(* le is a total order *)

\* 
\* The Boolean function btw is used to check the order
\* of identifiers. Because identifier order wraps around at zero, it
\* is meaningless to compare two identifiers—each precedes and
\* succeeds the other. This is why btw has three arguments
btw(x, y, z) == 
    IF x < z THEN ((x < y) /\ (y < z)) ELSE ((x < y) \/ (y < z))

(***************************************************************************)
(* Action: Send                                                            *)
(***************************************************************************)

Send(n, n1) ==
  /\ n \in Node
  /\ n1 \in Node
  /\ n # n1
  /\ \A Z \in Node : (Z # n /\ Z # n1) => btw(n, n1, Z)
  /\ pending' = [pending EXCEPT ![idn[n]][n1] = TRUE]
  /\ UNCHANGED <<leader, idn>>

(***************************************************************************)
(* Action: BecomeLeader                                                    *)
(***************************************************************************)

BecomeLeader(n) ==
  /\ n \in Node
  /\ pending[idn[n]][n]
  /\ leader' = [leader EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<pending, idn>>

(***************************************************************************)
(* Action: Receive                                                         *)
(***************************************************************************)

Receive(n, m, n1) ==
  /\ n \in Node
  /\ m \in Id
  /\ n1 \in Node
  /\ pending[m][n]
  /\ n # n1
  /\ \A Z \in Node : (Z # n /\ Z # n1) => btw(n, n1, Z)
  /\ IF idn[n] <= m
        THEN pending' = [pending EXCEPT ![m][n1] = TRUE]
        ELSE pending' = pending
  /\ UNCHANGED <<leader, idn>>

TypeOK ==
  /\ leader \in [Node -> BOOLEAN]
  /\ pending \in [Id -> [Node -> BOOLEAN]]
  /\ idn \in [Node -> Id]

(***************************************************************************)
(* Next operator                                                           *)
(***************************************************************************)

SendAction == TRUE /\ \E n \in Node : \E n1 \in Node : Send(n, n1)
BecomeLeaderAction == TRUE /\ \E n \in Node : BecomeLeader(n)
ReceiveAction == TRUE /\ \E n \in Node : \E m \in Id : \E n1 \in Node : Receive(n, m, n1)

Next ==
  \/ SendAction
  \/ BecomeLeaderAction
  \/ ReceiveAction


\* invariant [1000000] forall X: node, Y:node. leader(X) & leader(Y) -> X = Y  # at most one leader
LeaderSafety == \A n1,n2 \in Node : (leader[n1] /\ leader[n2]) => (n1 = n2)

NextUnchanged == UNCHANGED <<leader, pending, idn>>

CTICost == 0

====
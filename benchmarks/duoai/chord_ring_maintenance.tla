---- MODULE chord_ring_maintenance ----

EXTENDS Naturals, FiniteSets

(***************************************************************************)
(* Carrier and ring topology                                               *)
(***************************************************************************)

CONSTANTS NODE

(* org and other are distinct nodes in NODE *)
\* ASSUME org \in NODE /\ other \in NODE /\ org # other

\* ASSUME btw \subseteq NODE \X NODE \X NODE

\* (* Ring topology axioms: translate Ivy's module ring_topology(carrier) *)
\* ASSUME
\*   /\ \A W, X, Y, Z \in NODE :
\*         (Btw(W, X, Y) /\ Btw(W, Y, Z)) => Btw(W, X, Z)  \* transitive
\*   /\ \A W, X, Y \in NODE :
\*         Btw(W, X, Y) => ~Btw(W, Y, X)                   \* acyclic
\*   /\ \A W, X, Y \in NODE :
\*         Btw(W, X, Y) \/ Btw(W, Y, X) \/ W = X \/ X = Y  \* total
\*   /\ \A X, Y, Z \in NODE :
\*         (Btw(X, Y, Z) /\ X # Z) => Btw(Y, Z, X)         \* cyclic permutations

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)

VARIABLES
  a,        \* subset of NODE: active nodes
  s1,       \* subset of NODE × NODE: first successor relation
  in_s1,    \* subset of NODE: whether s1(x,·) is defined
  s2,       \* subset of NODE × NODE: second successor relation
  in_s2,    \* subset of NODE: whether s2(x,·) is defined
  p,        \* subset of NODE × NODE: predecessor relation
  reach,    \* subset of NODE: nodes that can reach org
  error,     \* subset of NODE: error nodes
  org,
  other

Vars == <<a, s1, in_s1, s2, in_s2, p, reach, error, org, other>>

(***************************************************************************)
(* Helpers                                                                 *)
(***************************************************************************)

IsActive(x) == x \in a

S1(x, y) == <<x, y>> \in s1
S2(x, y) == <<x, y>> \in s2
P(x, y)  == <<x, y>> \in p

(* Override all pairs whose first component is x with a new set of second components S *)
OverrideRow(R, x, S) ==
  { r \in R : r[1] # x }
  \cup { <<x, y>> : y \in S }

TypeInv ==
  /\ a \subseteq NODE
  /\ s1 \subseteq NODE \X NODE
  /\ s2 \subseteq NODE \X NODE
  /\ p  \subseteq NODE \X NODE
  /\ in_s1 \subseteq NODE
  /\ in_s2 \subseteq NODE
  /\ reach \subseteq NODE
  /\ error \subseteq NODE

(***************************************************************************)
(* Init                                                                    *)
(***************************************************************************)

\* TODO: Implement this behavior properly.
btw(x, y, z) == FALSE

Init ==
  /\ org    \in NODE
  /\ other  \in NODE /\ org # other
  /\ a      = {org, other}
  /\ s1     = {<<org, other>>, <<other, org>>}
  /\ in_s1  = {org, other}
  /\ s2     = {}     \* false
  /\ in_s2  = {}
  /\ p      = {<<org, other>>, <<other, org>>}
  /\ reach  = {org}
  /\ error  = {}


(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Join(x, y) ==
  /\ x \in NODE /\ y \in NODE
  /\ ~IsActive(x)
  /\ IsActive(y)
  /\ ~btw(x, org, y)
  /\ a'      = a \cup {x}
  /\ s1'     = OverrideRow(s1, x, {y})
  /\ in_s1'  = in_s1 \cup {x}
  /\ s2'     = OverrideRow(s2, x, {})
  /\ in_s2'  = in_s2 \ {x}
  /\ p'      = OverrideRow(p,  x, {})
  /\ reach'  = reach
  /\ error'  = error
  /\ UNCHANGED <<org, other>>

Stabilize(x, y, z) ==
  /\ x \in NODE /\ y \in NODE /\ z \in NODE
  /\ IsActive(x)
  /\ S1(x, y)
  /\ IsActive(y)
  /\ P(y, z)
  /\ btw(x, z, y)
  /\ a'      = a
  /\ s1'     = OverrideRow(s1, x, {z})
  /\ in_s1'  = in_s1 \cup {x}
  /\ s2'     = OverrideRow(s2, x, {y})
  /\ in_s2'  = in_s2 \cup {x}
  /\ p'      = p
  /\ reach'  = reach
  /\ error'  = error
  /\ UNCHANGED <<org, other>>


Notify(x, y, z) ==
  /\ x \in NODE /\ y \in NODE /\ z \in NODE
  /\ IsActive(x)
  /\ S1(x, y)
  /\ IsActive(y)
  /\ P(y, z) \/ (\A X \in NODE : ~P(y, X))
  /\ btw(z, x, y)
  /\ a'      = a
  /\ s1'     = s1
  /\ in_s1'  = in_s1
  /\ s2'     = s2
  /\ in_s2'  = in_s2
  /\ p'      = OverrideRow(p, y, {x})
  /\ reach'  = reach
  /\ error'  = error
  /\ UNCHANGED <<org, other>>

Inherit(x, y, z) ==
  /\ x \in NODE /\ y \in NODE /\ z \in NODE
  /\ IsActive(x)
  /\ S1(x, y)
  /\ IsActive(y)
  /\ S1(y, z)
  /\ a'      = a
  /\ s1'     = s1
  /\ in_s1'  = in_s1
  /\ s2'     = OverrideRow(s2, x, {z})
  /\ in_s2'  = in_s2 \cup {x}
  /\ p'      = p
  /\ reach'  = reach
  /\ error'  = error
  /\ UNCHANGED <<org, other>>
Remove(x, y, z) ==
  /\ x \in NODE /\ y \in NODE /\ z \in NODE
  /\ IsActive(x)
  /\ S1(x, y)
  /\ ~IsActive(y)
  /\ S2(x, z)
  /\ a'      = a
  /\ s1'     = OverrideRow(s1, x, {z})
  /\ in_s1'  = in_s1 \cup {x}
  /\ s2'     = OverrideRow(s2, x, {})
  /\ in_s2'  = in_s2 \ {x}
  /\ p'      = p
  /\ reach'  = reach
  /\ error'  = error
  /\ UNCHANGED <<org, other>>

Fail(x) ==
  /\ x \in NODE
  /\ IsActive(x)
  /\ x # org
  /\ \A Y \in NODE : S1(Y, x) => Y \in in_s2
  /\ \A Y, Z \in NODE :
        (S1(Y, x) /\ S2(Y, Z)) => IsActive(Z)
  /\ \A X, Y \in NODE :
        (S1(X, Y) /\ S2(X, x)) => (Y # x /\ IsActive(Y))
  /\ a'      = a \ {x}
  /\ p'      = OverrideRow(p,  x, {})
  /\ s1'     = OverrideRow(s1, x, {})
  /\ in_s1'  = in_s1 \ {x}
  /\ s2'     = OverrideRow(s2, x, {})
  /\ in_s2'  = in_s2 \ {x}
  /\ reach'  = reach
  /\ error'  = error
  /\ UNCHANGED <<org, other>>

ReachOrg(x, y, z) ==
  /\ x \in NODE /\ y \in NODE /\ z \in NODE
  /\ ( S1(x, y) /\ IsActive(y) /\ (y \in reach) )
     \/ ( S1(x, y) /\ ~IsActive(y) /\ S2(x, z) /\ IsActive(z) /\ (z \in reach) )
  /\ a'      = a
  /\ s1'     = s1
  /\ in_s1'  = in_s1
  /\ s2'     = s2
  /\ in_s2'  = in_s2
  /\ p'      = p
  /\ reach'  = reach \cup {x}
  /\ error'  = error
  /\ UNCHANGED <<org, other>>

RemoveOrg(x, y, z) ==
  /\ x \in NODE /\ y \in NODE /\ z \in NODE
  /\ x # org
  /\ S1(x, y)
  /\ (~IsActive(y)) \/ ~(y \in reach)
  /\ ~IsActive(y)
        => (\A Z \in NODE : ~S2(x, Z) \/ S2(x, z))
  /\ (~IsActive(y) /\ S2(x, z))
        => (~IsActive(z) \/ ~(z \in reach))
  /\ a'      = a
  /\ s1'     = s1
  /\ in_s1'  = in_s1
  /\ s2'     = s2
  /\ in_s2'  = in_s2
  /\ p'      = p
  /\ reach'  = reach \ {x}
  /\ error'  = error
  /\ UNCHANGED <<org, other>>
  
Test(x) ==
  /\ x \in NODE
  /\ \A X0, Y0 \in NODE :
        (S1(X0, Y0) /\ IsActive(Y0) /\ (Y0 \in reach))
          => X0 \in reach
  /\ \A X0, Y0, Z0 \in NODE :
        ( S1(X0, Y0) /\ ~IsActive(Y0)
          /\ S2(X0, Z0) /\ IsActive(Z0) /\ (Z0 \in reach) )
          => X0 \in reach
  /\ \A Y0 \in NODE :
        (btw(x, Y0, org) /\ IsActive(Y0)) => Y0 \in reach
  /\ IsActive(x)
  /\ x \notin reach
  /\ x \in in_s1 => \E Y0 \in NODE : S1(x, Y0)
  /\ x \in in_s2 => \E Y0 \in NODE : S2(x, Y0)
  /\ a'      = a
  /\ s1'     = s1
  /\ in_s1'  = in_s1
  /\ s2'     = s2
  /\ in_s2'  = in_s2
  /\ p'      = p
  /\ reach'  = reach
  /\ error'  = error \cup {x}
  /\ UNCHANGED <<org, other>>

(***************************************************************************)
(* Step relation                                                            *)
(***************************************************************************)

JoinStep      == \E x, y \in NODE : Join(x, y)
StabilizeStep == \E x, y, z \in NODE : Stabilize(x, y, z)
NotifyStep    == \E x, y, z \in NODE : Notify(x, y, z)
InheritStep   == \E x, y, z \in NODE : Inherit(x, y, z)
RemoveStep    == \E x, y, z \in NODE : Remove(x, y, z)
FailStep      == \E x \in NODE       : Fail(x)
ReachOrgStep  == \E x, y, z \in NODE : ReachOrg(x, y, z)
RemoveOrgStep == \E x, y, z \in NODE : RemoveOrg(x, y, z)
TestStep      == \E x \in NODE       : Test(x)

Next ==
  \/ JoinStep
  \/ StabilizeStep
  \/ NotifyStep
  \/ InheritStep
  \/ RemoveStep
  \/ FailStep
  \/ ReachOrgStep
  \/ RemoveOrgStep
  \/ TestStep
  \/ UNCHANGED Vars

Spec == Init /\ [][Next]_Vars /\ []TypeInv

(***************************************************************************)
(* Safety property corresponding to invariant [1000000] ~error(N)          *)
(***************************************************************************)

ErrorFree == \A n \in NODE : n \notin error

THEOREM Spec => []ErrorFree

=============================================================================
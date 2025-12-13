------------------------------ MODULE database_chain_replication ------------------------------

EXTENDS Naturals, FiniteSets

(***************************************************************************)
(* Constants and basic relations                                           *)
(***************************************************************************)

CONSTANTS
  TRANSACTION,
  NODE,
  KEY,
  OPERATION,

  zero,        \* distinguished transaction
  le,          \* subset of TRANSACTION × TRANSACTION
  op_reads_key,
  op_writes_key,
  op_node,
  node_for_key,
  op_in_tx,
  oporder

(***************************************************************************)
(* Relation helpers                                                        *)
(***************************************************************************)

Le(t1, t2)           == <<t1, t2>> \in le

OpReadsKey(op, k)    == <<op, k>> \in op_reads_key
OpWritesKey(op, k)   == <<op, k>> \in op_writes_key
OpNode(op, n)        == <<op, n>> \in op_node
NodeForKey(k, n)     == <<k,  n>> \in node_for_key
OpInTx(tx, op)       == <<tx, op>> \in op_in_tx
OpOrder(o1, o2)      == <<o1, o2>> \in oporder

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)

VARIABLES
  precommit_tx,   \* subset of TRANSACTION × NODE
  abort_tx,       \* subset of TRANSACTION
  commit_tx,      \* subset of TRANSACTION
  depends_tx,     \* subset of TRANSACTION × KEY × TRANSACTION
  read_tx,        \* subset of TRANSACTION × KEY
  write_tx        \* subset of TRANSACTION × KEY

Vars == <<precommit_tx, abort_tx, commit_tx, depends_tx, read_tx, write_tx>>

Precommit(tx, n) == <<tx, n>> \in precommit_tx
AbortTx(tx)      == tx \in abort_tx
CommitTx(tx)     == tx \in commit_tx
DependsTx(t1, k, t2) == <<t1, k, t2>> \in depends_tx
ReadTx(tx, k)    == <<tx, k>> \in read_tx
WriteTx(tx, k)   == <<tx, k>> \in write_tx

TypeOK ==
  /\ precommit_tx \subseteq TRANSACTION \X NODE
  /\ abort_tx     \subseteq TRANSACTION
  /\ commit_tx    \subseteq TRANSACTION
  /\ depends_tx   \subseteq TRANSACTION \X KEY \X TRANSACTION
  /\ read_tx      \subseteq TRANSACTION \X KEY
  /\ write_tx     \subseteq TRANSACTION \X KEY

(***************************************************************************)
(* Init                                                                    *)
(***************************************************************************)

Init ==
  /\ precommit_tx = { <<zero, n>> : n \in NODE }
  /\ abort_tx  = {}
  /\ commit_tx = { zero }
  /\ depends_tx = { <<zero, k, zero>> : k \in KEY }
  /\ read_tx = { <<zero, k>> : k \in KEY }
  /\ write_tx = { <<zero, k>> : k \in KEY }

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

DoAbort(tx, op, n, kw, kr, luwkw, lurkw, luwkr, lcwkr) ==
  /\ tx \in TRANSACTION /\ op \in OPERATION /\ n \in NODE
  /\ kw \in KEY /\ kr \in KEY
  /\ luwkw \in TRANSACTION /\ lurkw \in TRANSACTION
  /\ luwkr \in TRANSACTION /\ lcwkr \in TRANSACTION

  /\ OpInTx(tx, op)
  /\ ~AbortTx(tx) /\ ~CommitTx(tx)

  /\ \A X \in OPERATION, N \in NODE :
        (OpOrder(X, op) /\ X # op /\ OpNode(X, N))
          => Precommit(tx, N)

  /\ OpNode(op, n)
  /\ ~Precommit(tx, n)

  /\ \A K \in KEY : ~OpWritesKey(op, K) \/ OpWritesKey(op, kw)
  /\ OpWritesKey(op, kw) => NodeForKey(kw, n)

  /\ \A K \in KEY : ~OpReadsKey(op, K) \/ OpReadsKey(op, kr)
  /\ OpReadsKey(op, kr) => NodeForKey(kr, n)

  /\ WriteTx(luwkw, kw)
  /\ ~AbortTx(luwkw)
  /\ \A T \in TRANSACTION :
        WriteTx(T, kw) => (Le(T, luwkw) \/ AbortTx(T))

  /\ \E HT \in TRANSACTION :
       DependsTx(lurkw, kw, HT)
       /\ ~AbortTx(lurkw)
       /\ \A T \in TRANSACTION :
             ReadTx(T, kw) => (Le(T, lurkw) \/ AbortTx(T))

  /\ WriteTx(luwkr, kr)
  /\ Le(luwkr, tx)
  /\ ~AbortTx(luwkr)
  /\ \A T \in TRANSACTION :
        WriteTx(T, kr)
          => (Le(T, luwkr) \/ Le(tx, T) \/ AbortTx(T))

  /\ CommitTx(lcwkr)
  /\ WriteTx(lcwkr, kr)
  /\ Le(lcwkr, tx)
  /\ \A T \in TRANSACTION :
        (CommitTx(T) /\ WriteTx(T, kr))
          => (Le(T, lcwkr) \/ Le(tx, T))

  /\ ( (OpWritesKey(op, kw)
        /\ (Le(tx, luwkw) \/ Le(tx, lurkw)))
       \/
       (OpReadsKey(op, kr)
        /\ luwkr # lcwkr /\ Le(luwkr, tx)) )

  /\ abort_tx'    = abort_tx \cup {tx}
  /\ precommit_tx'= precommit_tx
  /\ commit_tx'   = commit_tx
  /\ depends_tx'  = depends_tx
  /\ read_tx'     = read_tx
  /\ write_tx'    = write_tx

DoProgress(tx, op, n, kw, kr, luwkw, lurkw, luwkr, lcwkr) ==
  /\ tx \in TRANSACTION /\ op \in OPERATION /\ n \in NODE
  /\ kw \in KEY /\ kr \in KEY
  /\ luwkw \in TRANSACTION /\ lurkw \in TRANSACTION
  /\ luwkr \in TRANSACTION /\ lcwkr \in TRANSACTION

  /\ OpInTx(tx, op)
  /\ ~AbortTx(tx) /\ ~CommitTx(tx)

  /\ \A X \in OPERATION, N \in NODE :
        (OpOrder(X, op) /\ X # op /\ OpNode(X, N))
          => Precommit(tx, N)

  /\ OpNode(op, n)
  /\ ~Precommit(tx, n)

  /\ \A K \in KEY : ~OpWritesKey(op, K) \/ OpWritesKey(op, kw)
  /\ OpWritesKey(op, kw) => NodeForKey(kw, n)

  /\ \A K \in KEY : ~OpReadsKey(op, K) \/ OpReadsKey(op, kr)
  /\ OpReadsKey(op, kr) => NodeForKey(kr, n)

  /\ WriteTx(luwkw, kw)
  /\ ~AbortTx(luwkw)
  /\ \A T \in TRANSACTION :
        WriteTx(T, kw) => (Le(T, luwkw) \/ AbortTx(T))

  /\ \E HT \in TRANSACTION :
       DependsTx(lurkw, kw, HT)
       /\ ~AbortTx(lurkw)
       /\ \A T \in TRANSACTION :
             ReadTx(T, kw) => (Le(T, lurkw) \/ AbortTx(T))

  /\ WriteTx(luwkr, kr)
  /\ Le(luwkr, tx)
  /\ ~AbortTx(luwkr)
  /\ \A T \in TRANSACTION :
        WriteTx(T, kr)
          => (Le(T, luwkr) \/ Le(tx, T) \/ AbortTx(T))

  /\ CommitTx(lcwkr)
  /\ WriteTx(lcwkr, kr)
  /\ Le(lcwkr, tx)
  /\ \A T \in TRANSACTION :
        (CommitTx(T) /\ WriteTx(T, kr))
          => (Le(T, lcwkr) \/ Le(tx, T))

  /\ ~((OpWritesKey(op, kw)
         /\ (Le(tx, luwkw) \/ Le(tx, lurkw)))
       \/
       (OpReadsKey(op, kr)
         /\ luwkr # lcwkr /\ Le(luwkr, tx)))

  /\ write_tx'
       = write_tx
         \cup (IF OpWritesKey(op, kw)
               THEN {<<tx, kw>>}
               ELSE {})

  /\ depends_tx'
       = depends_tx
         \cup (IF OpReadsKey(op, kr)
               THEN {<<tx, kr, lcwkr>>}
               ELSE {})

  /\ read_tx'
       = read_tx
         \cup (IF OpReadsKey(op, kr)
               THEN {<<tx, kr>>}
               ELSE {})

  /\ precommit_tx' = precommit_tx \cup {<<tx, n>>}
  /\ abort_tx' = abort_tx
  /\ LET LastOp ==
         \A O \in OPERATION : OpOrder(op, O) => O = op
     IN commit_tx'
          = commit_tx
            \cup (IF LastOp THEN {tx} ELSE {})

(***************************************************************************)
(* Step and spec                                                           *)
(***************************************************************************)

Next ==
  \/ \E tx \in TRANSACTION, op \in OPERATION,
        n \in NODE, kw, kr \in KEY,
        luwkw, lurkw, luwkr, lcwkr \in TRANSACTION :
        DoAbort(tx, op, n, kw, kr, luwkw, lurkw, luwkr, lcwkr)
  \/ \E tx \in TRANSACTION, op \in OPERATION,
        n \in NODE, kw, kr \in KEY,
        luwkw, lurkw, luwkr, lcwkr \in TRANSACTION :
        DoProgress(tx, op, n, kw, kr, luwkw, lurkw, luwkr, lcwkr)

(***************************************************************************)
(* Safety: Linearizability + Atomicity (Ivy invariant)                     *)
(***************************************************************************)

LinSafety ==
  /\ \A TX1, TX2 \in TRANSACTION,
        K \in KEY,
        T3 \in TRANSACTION :
        ~(
          TX1 # TX2
          /\ CommitTx(TX1)
          /\ CommitTx(TX2)
          /\ Le(TX1, TX2)
          /\ WriteTx(TX1, K)
          /\ DependsTx(TX2, K, T3)
          /\ ~Le(TX1, T3)
        )
  /\ \A T \in TRANSACTION,
        O \in OPERATION,
        N \in NODE :
        (CommitTx(T) /\ OpInTx(T, O) /\ OpNode(O, N))
          => Precommit(T, N)


CTICost == 0
=============================================================================
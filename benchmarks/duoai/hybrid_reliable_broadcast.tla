---------- MODULE hybrid_reliable_broadcast ------------------------------

EXTENDS FiniteSets, TLC

(***************************************************************************)
(* Constants: universe + quorum structure                                  *)
(***************************************************************************)

CONSTANTS
  NODE


\* MemberA(n, qa) == <<n, qa>> \in member_a
\* MemberB(n, qb) == <<n, qb>> \in member_b

\* MemberFC(n) == n \in member_fc
\* MemberFI(n) == n \in member_fi
\* MemberFS(n) == n \in member_fs
\* MemberFA(n) == n \in member_fa

(***************************************************************************)
(* State                                                                   *)
(***************************************************************************)

VARIABLES
  rcv_init,        \* subset NODE
  accept,          \* subset NODE
  sent_msg,        \* subset NODE × NODE   (src,dst)
  rcv_msg,         \* subset NODE × NODE   (src,dst)
  sent_msg_tmp,    \* subset NODE × NODE   (temporary copy)
  sent_msg_proj,    \* subset NODE          (projection of sent_msg)
  quorum_A,
  quorum_B,
  member_fc,  \* subsets of NODE (faulty classes)
  member_fi,
  member_fs,
  member_fa

Vars == <<rcv_init, accept, sent_msg, rcv_msg, sent_msg_tmp, sent_msg_proj, quorum_A, quorum_B, member_fc, member_fi, member_fs, member_fa>>

RcvInit(n) == n \in rcv_init
Accept(n)  == n \in accept

SentMsg(s, d) == <<s, d>> \in sent_msg
RcvMsg(s, d)  == <<s, d>> \in rcv_msg
TmpMsg(s, d)  == <<s, d>> \in sent_msg_tmp

SentMsgProj(n) == n \in sent_msg_proj

TypeOK ==
  /\ rcv_init      \subseteq NODE
  /\ accept        \subseteq NODE
  /\ sent_msg      \subseteq NODE \X NODE
  /\ rcv_msg       \subseteq NODE \X NODE
  /\ sent_msg_tmp  \subseteq NODE \X NODE
  /\ sent_msg_proj \subseteq NODE

(***************************************************************************)
(* Init                                                                    *)
(***************************************************************************)

Init ==
  /\ accept        = {}
  /\ sent_msg      = {}
  /\ sent_msg_proj = {}
  /\ rcv_msg       = {}
  /\ sent_msg_tmp  = {}
  /\ rcv_init = [n \in NODE |-> FALSE]
  \* fc, fi, fs, fa are subsets of NODE
  \* fc,fi,fs,fa are disjoint
  /\ member_fc \in SUBSET NODE
  /\ member_fi \in SUBSET NODE
  /\ member_fc \intersect member_fi = {}
  /\ member_fs \in SUBSET NODE
  /\ member_fi \intersect member_fs = {}
  /\ member_fc \intersect member_fs = {}
  /\ member_fa \in SUBSET NODE
  /\ member_fc \intersect member_fa = {}
  /\ member_fi \intersect member_fa = {}
  /\ member_fs \intersect member_fa = {}
  \* Define quorums and their properties.
  /\ quorum_A \in SUBSET {s \in SUBSET NODE : s # {}}
  /\ quorum_B \in SUBSET {s \in SUBSET NODE : s # {}}
  \* axiom exists B:quorum_b. forall N:node. member_b(N, B) -> !member_fa(N) & !member_fc(N) & !member_fs(N) & !member_fi(N)
  /\ \E B \in quorum_B : \A n \in NODE : n \in B => (n \notin member_fa /\ n \notin member_fc /\ n \notin member_fs /\ n \notin member_fi)
  \* axiom forall A_BP:quorum_a. exists N:node. member_a(N, A_BP) & ~member_fa(N) & ~member_fs(N)
  /\ \A A \in quorum_A : \E n \in NODE : n \in A /\ n \notin member_fa /\ n \notin member_fs
  \* axiom forall B_CF:quorum_b. exists A:quorum_a. forall N:node. member_a(N, A) -> member_b(N, B_CF) & ~member_fa(N) & ~member_fi(N)
  /\ \A B \in quorum_B : \E A \in quorum_A : \A n \in NODE : n \in A => n \in B /\ n \notin member_fa /\ n \notin member_fi


(***************************************************************************)
(* Helpers                                                                 *)
(***************************************************************************)

(* set all outgoing messages from n to true, preserving others *)
AddAllFrom(n, R) ==
  R \cup { <<n, d>> : d \in NODE }

(* update sent_msg_proj(n) := (∃d. SentMsg'(n,d)) *)
UpdateProj(n, projSet, newSent) ==
  (projSet \ {n})
    \cup (IF \E d \in NODE : <<n,d>> \in newSent THEN {n} ELSE {})

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

(*** Correct nodes ***)

ReceiveInit(n) ==
  /\ rcv_init[n]
  /\ LET newSent == AddAllFrom(n, sent_msg)
     IN /\ sent_msg'      = newSent
        /\ sent_msg_proj' = sent_msg_proj \cup {n}
        /\ rcv_msg'       = rcv_msg
        /\ rcv_init'      = rcv_init
        /\ sent_msg_tmp'  = sent_msg_tmp
        /\ accept'        = accept
        /\ UNCHANGED <<quorum_A, quorum_B, member_fc, member_fi, member_fs, member_fa>>

ReceiveMsg(n, s) ==
  /\ SentMsg(s, n)
  /\ LET newRcv == rcv_msg \cup {<<s, n>>} IN
     LET condB ==
           \E B \in quorum_B :
             \A N \in NODE : N \in B => <<N, n>> \in newRcv
         condA ==
           \E A \in quorum_A :
             \A N \in NODE :N \in A => <<N, n>> \in newRcv
         newAcc ==
           IF condB THEN accept \cup {n} ELSE accept
         newSent ==
           IF condA THEN AddAllFrom(n, sent_msg) ELSE sent_msg
         newProj ==
           IF condA THEN sent_msg_proj \cup {n} ELSE sent_msg_proj
     IN /\ rcv_msg'       = newRcv
        /\ accept'        = newAcc
        /\ sent_msg'      = newSent
        /\ sent_msg_proj' = newProj
        /\ rcv_init'      = rcv_init
        /\ sent_msg_tmp'  = sent_msg_tmp
        /\ UNCHANGED <<quorum_A, quorum_B, member_fc, member_fi, member_fs, member_fa>>


(*** fc – symmetric omission ***)

ReceiveMsg_c_1(n, s) ==
  /\ n \in NODE /\ s \in NODE
  /\ n \in member_fc
  /\ SentMsg(s, n)
  /\ \E A \in quorum_A :
       \A N \in NODE :
         N \in A => (RcvMsg(N, n) \/ N = s)
  /\ LET newRcv == rcv_msg \cup {<<s, n>>} IN
     LET condB ==
           \E B \in quorum_B :
             \A N \in NODE : N \in B => <<N, n>> \in newRcv
         newAcc ==
           IF condB THEN accept \cup {n} ELSE accept
         newSent == AddAllFrom(n, sent_msg)
         newProj == sent_msg_proj \cup {n}
     IN /\ rcv_msg'       = newRcv
        /\ accept'        = newAcc
        /\ sent_msg'      = newSent
        /\ sent_msg_proj' = newProj
        /\ rcv_init'      = rcv_init
        /\ sent_msg_tmp'  = sent_msg_tmp
        /\ UNCHANGED <<quorum_A, quorum_B, member_fc, member_fi, member_fs, member_fa>>


ReceiveMsg_c_2(n, s) ==
  /\ n \in NODE /\ s \in NODE
  /\ n \in member_fc
  /\ SentMsg(s, n)
  /\ LET newRcv == rcv_msg \cup {<<s, n>>} IN
     LET condB ==
           \E B \in quorum_B :
             \A N \in NODE : N \in B => <<N, n>> \in newRcv
         newAcc ==
           IF condB THEN accept \cup {n} ELSE accept
     IN /\ rcv_msg'       = newRcv
        /\ accept'        = newAcc
        /\ sent_msg'      = sent_msg
        /\ sent_msg_proj' = sent_msg_proj
        /\ rcv_init'      = rcv_init
        /\ sent_msg_tmp'  = sent_msg_tmp
        /\ UNCHANGED <<quorum_A, quorum_B, member_fc, member_fi, member_fs, member_fa>>


(*** fi – arbitrary omission ***)

ReceiveInit_i(n) ==
  /\ n \in NODE
  /\ n \in member_fi
  /\ RcvInit(n)
  /\ sent_msg_tmp' = sent_msg
  /\ sent_msg' \subseteq NODE \X NODE
  /\ \A S \in NODE, D \in NODE :
       S # n => (<<S, D>> \in sent_msg' <=> <<S, D>> \in sent_msg)
  /\ \A D \in NODE :
       (<<n, D>> \in sent_msg) => <<n, D>> \in sent_msg'
  /\ ( ~SentMsgProj(n)
       \/ \E D \in NODE : <<n, D>> \in sent_msg' )
  /\ sent_msg_proj'
       = UpdateProj(n, sent_msg_proj, sent_msg')
  /\ rcv_msg'      = rcv_msg
  /\ rcv_init'     = rcv_init
  /\ accept'       = accept
  /\ UNCHANGED <<quorum_A, quorum_B, member_fc, member_fi, member_fs, member_fa>>


ReceiveMsg_i(n, s) ==
  /\ n \in NODE /\ s \in NODE
  /\ n \in member_fi
  /\ SentMsg(s, n)
  /\ LET newRcv == rcv_msg \cup {<<s, n>>} IN
     LET condB ==
           \E B \in quorum_B :
             \A N \in NODE : N \in B => <<N, n>> \in newRcv
         condA ==
           \E A \in quorum_A :
             \A N \in NODE : N \in A => <<N, n>> \in newRcv
         newAcc ==
           IF condB THEN accept \cup {n} ELSE accept
     IN
     /\ rcv_msg'  = newRcv
     /\ accept'   = newAcc
     /\ IF ~condA
        THEN /\ sent_msg'      = sent_msg
             /\ sent_msg_tmp'  = sent_msg_tmp
             /\ sent_msg_proj' = sent_msg_proj
        ELSE /\ sent_msg_tmp' = sent_msg
             /\ sent_msg' \subseteq NODE \X NODE
             /\ \A S \in NODE, D \in NODE :
                  S # n => (<<S, D>> \in sent_msg' <=> <<S, D>> \in sent_msg)
             /\ \A D \in NODE :
                  (<<n, D>> \in sent_msg) => <<n, D>> \in sent_msg'
             /\ ( ~SentMsgProj(n)
                  \/ \E D \in NODE : <<n, D>> \in sent_msg' )
             /\ sent_msg_proj'
                  = UpdateProj(n, sent_msg_proj, sent_msg')
     /\ rcv_init' = rcv_init
     /\ UNCHANGED <<quorum_A, quorum_B, member_fc, member_fi, member_fs, member_fa>>

(*** fs – symmetric Byzantine ***)

FaultySend_s(n) ==
  /\ n \in NODE
  /\ n \in member_fs
  /\ sent_msg'      = AddAllFrom(n, sent_msg)
  /\ sent_msg_proj' = sent_msg_proj \cup {n}
  /\ rcv_msg'       = rcv_msg
  /\ rcv_init'      = rcv_init
  /\ sent_msg_tmp'  = sent_msg_tmp
  /\ accept'        = accept
  /\ UNCHANGED <<quorum_A, quorum_B, member_fc, member_fi, member_fs, member_fa>>

FaultyState_sa(n) ==
  /\ n \in NODE
  /\ (n \in member_fs \/ n \in member_fa)
  \* arbitrary new rcv_msg and accept (Byzantine)
  /\ rcv_msg'  \in (SUBSET (NODE \X NODE))
  /\ accept'   \in (SUBSET NODE)
  /\ sent_msg'      = sent_msg
  /\ sent_msg_tmp'  = sent_msg_tmp
  /\ sent_msg_proj' = sent_msg_proj
  /\ rcv_init'      = rcv_init
  /\ UNCHANGED <<quorum_A, quorum_B, member_fc, member_fi, member_fs, member_fa>>

(*** fa – arbitrary Byzantine ***)

FaultySend_a(n) ==
  /\ n \in NODE
  /\ n \in member_fa
  /\ sent_msg_tmp' = sent_msg
  /\ sent_msg' \in (SUBSET (NODE \X NODE))
  /\ \A S \in NODE, D \in NODE :
       S # n => (<<S, D>> \in sent_msg' <=> <<S, D>> \in sent_msg)
  /\ \A D \in NODE :
       (<<n, D>> \in sent_msg) => <<n, D>> \in sent_msg'
  /\ ( ~SentMsgProj(n)
       \/ \E D \in NODE : <<n, D>> \in sent_msg' )
  /\ sent_msg_proj'
       = UpdateProj(n, sent_msg_proj, sent_msg')
  /\ rcv_msg'  = rcv_msg
  /\ rcv_init' = rcv_init
  /\ accept'   = accept
  /\ UNCHANGED <<quorum_A, quorum_B, member_fc, member_fi, member_fs, member_fa>>

(***************************************************************************)
(* Next and Spec                                                           *)
(***************************************************************************)

Next ==
  \/ \E n \in NODE : ReceiveInit(n)
  \/ \E n, s \in NODE : ReceiveMsg(n, s)
  \/ \E n, s \in NODE : ReceiveMsg_c_1(n, s)
  \/ \E n, s \in NODE : ReceiveMsg_c_2(n, s)
  \/ \E n \in NODE : ReceiveInit_i(n)
  \/ \E n, s \in NODE : ReceiveMsg_i(n, s)
  \/ \E n \in NODE : FaultySend_s(n)
  \/ \E n \in NODE : FaultyState_sa(n)
  \/ \E n \in NODE : FaultySend_a(n)

Spec == Init /\ [][Next]_Vars

(***************************************************************************)
(* Safety property                                                         *)
(***************************************************************************)

Safety ==
  \A Nacc \in NODE :
        ( ~Nacc \in member_fs /\ ~Nacc \in member_fa /\ Accept(Nacc) )
      => \E N0 \in NODE :
           ~N0 \in member_fs /\ ~N0 \in member_fa /\ rcv_init[N0]

THEOREM Spec => []Safety

Symmetry == Permutations(NODE)

=============================================================================
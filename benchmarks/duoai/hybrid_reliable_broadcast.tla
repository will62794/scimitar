---------- MODULE hybrid_reliable_broadcast ------------------------------

EXTENDS FiniteSets

(***************************************************************************)
(* Constants: universe + quorum structure                                  *)
(***************************************************************************)

CONSTANTS
  NODE,
  QUORUM_A,
  QUORUM_B,

  member_a,   \* subset of NODE × QUORUM_A
  member_b,   \* subset of NODE × QUORUM_B

  member_fc,  \* subsets of NODE (faulty classes)
  member_fi,
  member_fs,
  member_fa

MemberA(n, qa) == <<n, qa>> \in member_a
MemberB(n, qb) == <<n, qb>> \in member_b

MemberFC(n) == n \in member_fc
MemberFI(n) == n \in member_fi
MemberFS(n) == n \in member_fs
MemberFA(n) == n \in member_fa

ASSUME
  /\ member_a  \subseteq NODE \X QUORUM_A
  /\ member_b  \subseteq NODE \X QUORUM_B
  /\ member_fc \subseteq NODE
  /\ member_fi \subseteq NODE
  /\ member_fs \subseteq NODE
  /\ member_fa \subseteq NODE

  \* ∃B:quorum_b. ∀N. member_b(N,B) -> ~fa & ~fc & ~fs & ~fi
  /\ \E B \in QUORUM_B :
       \A N \in NODE :
         MemberB(N, B)
           => ~MemberFA(N) /\ ~MemberFC(N) /\ ~MemberFS(N) /\ ~MemberFI(N)

  \* ∀A_BP. ∃N. member_a(N, A_BP) & ~fa & ~fs
  /\ \A A_BP \in QUORUM_A :
       \E N \in NODE :
         MemberA(N, A_BP)
           /\ ~MemberFA(N) /\ ~MemberFS(N)

  \* ∀B_CF. ∃A. ∀N. member_a(N,A) -> member_b(N,B_CF) & ~fa & ~fi
  /\ \A B_CF \in QUORUM_B :
       \E A \in QUORUM_A :
         \A N \in NODE :
           MemberA(N, A)
             => MemberB(N, B_CF)
               /\ ~MemberFA(N) /\ ~MemberFI(N)

  \* fc,fi,fs,fa disjoint
  /\ \A N \in NODE :
        ~ (MemberFC(N) /\ MemberFI(N))
      /\ ~ (MemberFC(N) /\ MemberFS(N))
      /\ ~ (MemberFC(N) /\ MemberFA(N))
      /\ ~ (MemberFI(N) /\ MemberFS(N))
      /\ ~ (MemberFI(N) /\ MemberFA(N))
      /\ ~ (MemberFS(N) /\ MemberFA(N))

(***************************************************************************)
(* State                                                                   *)
(***************************************************************************)

VARIABLES
  rcv_init,        \* subset NODE
  accept,          \* subset NODE
  sent_msg,        \* subset NODE × NODE   (src,dst)
  rcv_msg,         \* subset NODE × NODE   (src,dst)
  sent_msg_tmp,    \* subset NODE × NODE   (temporary copy)
  sent_msg_proj    \* subset NODE          (projection of sent_msg)

Vars == <<rcv_init, accept, sent_msg, rcv_msg, sent_msg_tmp, sent_msg_proj>>

RcvInit(n) == n \in rcv_init
Accept(n)  == n \in accept

SentMsg(s, d) == <<s, d>> \in sent_msg
RcvMsg(s, d)  == <<s, d>> \in rcv_msg
TmpMsg(s, d)  == <<s, d>> \in sent_msg_tmp

SentMsgProj(n) == n \in sent_msg_proj

TypeInv ==
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
  /\ TypeInv
  /\ accept        = {}
  /\ sent_msg      = {}
  /\ sent_msg_proj = {}
  /\ rcv_msg       = {}
  /\ sent_msg_tmp  = {}
  \* rcv_init is arbitrary subset of NODE
  /\ rcv_init \subseteq NODE

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
  /\ n \in NODE
  /\ RcvInit(n)
  /\ LET newSent == AddAllFrom(n, sent_msg)
     IN /\ sent_msg'      = newSent
        /\ sent_msg_proj' = sent_msg_proj \cup {n}
        /\ rcv_msg'       = rcv_msg
        /\ rcv_init'      = rcv_init
        /\ sent_msg_tmp'  = sent_msg_tmp
        /\ accept'        = accept

ReceiveMsg(n, s) ==
  /\ n \in NODE /\ s \in NODE
  /\ SentMsg(s, n)
  /\ LET newRcv == rcv_msg \cup {<<s, n>>} IN
     LET condB ==
           \E B \in QUORUM_B :
             \A N \in NODE : MemberB(N, B) => <<N, n>> \in newRcv
         condA ==
           \E A \in QUORUM_A :
             \A N \in NODE : MemberA(N, A) => <<N, n>> \in newRcv
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

(*** fc – symmetric omission ***)

ReceiveMsg_c_1(n, s) ==
  /\ n \in NODE /\ s \in NODE
  /\ MemberFC(n)
  /\ SentMsg(s, n)
  /\ \E A \in QUORUM_A :
       \A N \in NODE :
         MemberA(N, A) => (RcvMsg(N, n) \/ N = s)
  /\ LET newRcv == rcv_msg \cup {<<s, n>>} IN
     LET condB ==
           \E B \in QUORUM_B :
             \A N \in NODE : MemberB(N, B) => <<N, n>> \in newRcv
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

ReceiveMsg_c_2(n, s) ==
  /\ n \in NODE /\ s \in NODE
  /\ MemberFC(n)
  /\ SentMsg(s, n)
  /\ LET newRcv == rcv_msg \cup {<<s, n>>} IN
     LET condB ==
           \E B \in QUORUM_B :
             \A N \in NODE : MemberB(N, B) => <<N, n>> \in newRcv
         newAcc ==
           IF condB THEN accept \cup {n} ELSE accept
     IN /\ rcv_msg'       = newRcv
        /\ accept'        = newAcc
        /\ sent_msg'      = sent_msg
        /\ sent_msg_proj' = sent_msg_proj
        /\ rcv_init'      = rcv_init
        /\ sent_msg_tmp'  = sent_msg_tmp

(*** fi – arbitrary omission ***)

ReceiveInit_i(n) ==
  /\ n \in NODE
  /\ MemberFI(n)
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

ReceiveMsg_i(n, s) ==
  /\ n \in NODE /\ s \in NODE
  /\ MemberFI(n)
  /\ SentMsg(s, n)
  /\ LET newRcv == rcv_msg \cup {<<s, n>>} IN
     LET condB ==
           \E B \in QUORUM_B :
             \A N \in NODE : MemberB(N, B) => <<N, n>> \in newRcv
         condA ==
           \E A \in QUORUM_A :
             \A N \in NODE : MemberA(N, A) => <<N, n>> \in newRcv
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

(*** fs – symmetric Byzantine ***)

FaultySend_s(n) ==
  /\ n \in NODE
  /\ MemberFS(n)
  /\ sent_msg'      = AddAllFrom(n, sent_msg)
  /\ sent_msg_proj' = sent_msg_proj \cup {n}
  /\ rcv_msg'       = rcv_msg
  /\ rcv_init'      = rcv_init
  /\ sent_msg_tmp'  = sent_msg_tmp
  /\ accept'        = accept

FaultyState_sa(n) ==
  /\ n \in NODE
  /\ (MemberFS(n) \/ MemberFA(n))
  \* arbitrary new rcv_msg and accept (Byzantine)
  /\ rcv_msg'  \subseteq NODE \X NODE
  /\ accept'   \subseteq NODE
  /\ sent_msg'      = sent_msg
  /\ sent_msg_tmp'  = sent_msg_tmp
  /\ sent_msg_proj' = sent_msg_proj
  /\ rcv_init'      = rcv_init

(*** fa – arbitrary Byzantine ***)

FaultySend_a(n) ==
  /\ n \in NODE
  /\ MemberFA(n)
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
  /\ rcv_msg'  = rcv_msg
  /\ rcv_init' = rcv_init
  /\ accept'   = accept

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
  \/ UNCHANGED Vars

Spec == Init /\ [][Next]_Vars

(***************************************************************************)
(* Safety property                                                         *)
(***************************************************************************)

Safety ==
  \A Nacc \in NODE :
    ( ~MemberFS(Nacc) /\ ~MemberFA(Nacc) /\ Accept(Nacc) )
      => \E N0 \in NODE :
           ~MemberFS(N0) /\ ~MemberFA(N0) /\ RcvInit(N0)

THEOREM Spec => []Safety

=============================================================================
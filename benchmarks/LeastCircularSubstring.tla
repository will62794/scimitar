---------------------- MODULE LeastCircularSubstring ------------------------
(***************************************************************************)
(* An implementation of the lexicographically-least circular substring     *)
(* algorithm from the 1980 paper by Kellogg S. Booth. See:                 *)
(* https://doi.org/10.1016/0020-0190(80)90149-0                            *)
(***************************************************************************)

\* source: https://github.com/tlaplus/Examples/tree/master/specifications/LeastCircularSubstring

EXTENDS Integers, ZSequences, TLC

\* CONSTANTS CharacterSet

\* ASSUME CharacterSet \subseteq Nat

VARIABLES var_b, var_n, var_f, var_i, var_j, var_k, var_pc

CONSTANTS CharSetSize, MaxStringLength

MCCharacterSet == 0 .. (CharSetSize - 1)

(* define statement *)
Corpus == ZSeq(MCCharacterSet)
nil == -1


vars == << var_b, var_n, var_f, var_i, var_j, var_k, var_pc >>

Init == (* Global variables *)
        /\ var_b \in Corpus
        /\ var_n = ZLen(var_b)
        /\ var_f = [index \in 0..2*var_n |-> nil]
        /\ var_i = nil
        /\ var_j = 1
        /\ var_k = 0
        /\ var_pc = "L3"

L3 == /\ var_pc = "L3"
      /\ IF var_j < 2 * var_n
            THEN /\ var_pc' = "L5"
            ELSE /\ var_pc' = "Done"
      /\ UNCHANGED << var_b, var_n, var_f, var_i, var_j, var_k >>

L5 == /\ var_pc = "L5"
      /\ var_i' = var_f[var_j - var_k - 1]
      /\ var_pc' = "L6"
      /\ UNCHANGED << var_b, var_n, var_f, var_j, var_k >>

L6 == /\ var_pc = "L6"
      /\ IF var_b[var_j % var_n] /= var_b[(var_k + var_i + 1) % var_n] /\ var_i /= nil
            THEN /\ var_pc' = "L7"
            ELSE /\ var_pc' = "L10"
      /\ UNCHANGED << var_b, var_n, var_f, var_i, var_j, var_k >>

L7 == /\ var_pc = "L7"
      /\ IF var_b[var_j % var_n] < var_b[(var_k + var_i + 1) % var_n]
            THEN /\ var_pc' = "L8"
            ELSE /\ var_pc' = "L9"
      /\ UNCHANGED << var_b, var_n, var_f, var_i, var_j, var_k >>

L8 == /\ var_pc = "L8"
      /\ var_k' = var_j - var_i - 1
      /\ var_pc' = "L9"
      /\ UNCHANGED << var_b, var_n, var_f, var_i, var_j >>

L9 == /\ var_pc = "L9"
      /\ var_i' = var_f[var_j - var_k - 1]
      /\ var_pc' = "L6"
      /\ UNCHANGED << var_b, var_n, var_f, var_j, var_k >>

L10 == /\ var_pc = "L10"
       /\ IF var_b[var_j % var_n] /= var_b[(var_k + var_i + 1) % var_n] /\ var_i = nil
             THEN /\ var_pc' = "L11"
             ELSE /\ var_pc' = "L14"
       /\ UNCHANGED << var_b, var_n, var_f, var_i, var_j, var_k >>

L11 == /\ var_pc = "L11"
       /\ IF var_b[var_j % var_n] < var_b[(var_k + var_i + 1) % var_n]
             THEN /\ var_pc' = "L12"
             ELSE /\ var_pc' = "L13"
       /\ UNCHANGED << var_b, var_n, var_f, var_i, var_j, var_k >>

L12 == /\ var_pc = "L12"
       /\ var_k' = var_j
       /\ var_pc' = "L13"
       /\ UNCHANGED << var_b, var_n, var_f, var_i, var_j >>

L13 == /\ var_pc = "L13"
       /\ var_f' = [var_f EXCEPT ![var_j - var_k] = nil]
       /\ var_pc' = "LVR"
       /\ UNCHANGED << var_b, var_n, var_f, var_i, var_j, var_k >>

L14 == /\ var_pc = "L14"
       /\ var_f' = [var_f EXCEPT ![var_j - var_k] = var_i + 1]
       /\ var_pc' = "LVR"
       /\ UNCHANGED << var_b, var_n, var_f, var_i, var_j, var_k >>

LVR == /\ var_pc = "LVR"
       /\ var_j' = var_j + 1
       /\ var_pc' = "L3"
       /\ UNCHANGED << var_b, var_n, var_f, var_i, var_k >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == var_pc = "Done" /\ UNCHANGED vars

L3Action == TRUE /\ L3
L5Action == TRUE /\ L5
L6Action == TRUE /\ L6
L7Action == TRUE /\ L7
L8Action == TRUE /\ L8
L9Action == TRUE /\ L9
L10Action == TRUE /\ L10
L11Action == TRUE /\ L11
L12Action == TRUE /\ L12
L13Action == TRUE /\ L13
L14Action == TRUE /\ L14
LVRAction == TRUE /\ LVR

Next == 
    \/ L3Action 
    \/ L5Action 
    \/ L6Action 
    \/ L7Action 
    \/ L8Action 
    \/ L9Action 
    \/ L10Action 
    \/ L11Action 
    \/ L12Action 
    \/ L13Action 
    \/ L14Action 
    \/ LVRAction
    \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(var_pc = "Done")

\* END TRANSLATION 

TypeOK ==
  /\ var_b \in Corpus /\ ZLen(var_b) > 0
  /\ var_n = ZLen(var_b)
  /\ var_f \in [0..2*var_n -> 0..2*var_n \cup {nil}]
  /\ var_i \in 0..2*var_n \cup {nil}
  /\ var_j \in 0..2*var_n \cup {1}
  /\ var_k \in ZIndices(var_b) \cup {0}
  /\ var_pc \in {"L3", "L5", "L6", "L7", "L8", "L9", "L10", "L11", "L12", "L13", "L14", "LVR", "Done"}

\* Is this shift the lexicographically-minimal rotation?
IsLeastMinimalRotation(s, r) == 
  LET rotation == Rotation(s, r) IN
  /\ \A other \in Rotations(s) :
    /\ rotation \preceq other.seq
    /\ rotation = other.seq => (r <= other.shift)

Correctness ==
  (var_pc = "Done") => IsLeastMinimalRotation(var_b, var_k)


ZSeqNat == 0 .. MaxStringLength

CTICost == 0

NextUnchanged == UNCHANGED << var_b, var_n, var_f, var_i, var_j, var_k >>

=============================================================================


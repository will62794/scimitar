---- MODULE quant_parse_test ----
EXTENDS TLC, Naturals

CONSTANT Node

VARIABLE x,y

Add(adda,addb) == adda + addb

A1(ni) == 
    /\ x > 0
    /\ x[ni] = 1
    /\ x[ni] = Add(2,ni)
    /\ x' = [x EXCEPT ![ni] = Add(x[ni],y)]
    /\ UNCHANGED <<y>>

A2(nj) == 
    /\ x < 13
    /\ x' = [x EXCEPT ![nj] = x[nj] + y]
    /\ y' = y + 1

A1Action == \E nquantarg \in Node : A1(nquantarg)
\* A2Action == \E n \in Node : A2(n)

Next == 
    \/ A1Action
    \* \/ A2Action
====

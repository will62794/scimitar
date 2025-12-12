---- MODULE chord_ring_maintenance_anim ----
EXTENDS TLC, SVG, chord_ring_maintenance






\* \* 
\* \* Visualizations.
\* \* 
\* LogEdges(s) == {<< <<i, log[s][i]>>, <<i+1, log[s][i+1]>> >> : i \in (DOMAIN log[s] \ {Len(log[s])})}
\* LogTreeEdges == UNION {LogEdges(s) : s \in Server}
\* LogNodes(s) == {<<i, log[s][i]>> : i \in DOMAIN log[s]}
\* LogTreeNodes == UNION {LogNodes(s) : s \in Server}



\* Edges can also be specified as tuples of length > 2, such as <<n1,n2,x,y,z>>,
\* which defines an edge between n1 -> n2, but x,y,z define additional metadata
\* specific to that edge e.g. this also allows for multiple edges between the
\* same nodes in the same direction, but with potentially different edge
\* "types".
graphAttrs == ("rankdir" :> "LR")
DiGraph(V, E, nodeAttrsFn, edgeAttrsFn) == SVGElem("digraph", [V |-> V, E |-> E, nodeAttrsFn |-> nodeAttrsFn, edgeAttrsFn |-> edgeAttrsFn, graphAttrs |-> graphAttrs], <<>>, "")


Nodes == {n : n \in NODE}
Edges == s1 \cup s2




\* Graphviz attributes
nodeAttrsFn(n) == 
    [
    label |-> ToString(n),
    color |-> "black",
    fillcolor |-> IF n = org THEN "lightgreen" ELSE "white",
    penwidth |-> "2",
    fontsize |-> "12",
    shape |-> "circle", 
    style |-> "filled"
]

edgeAttrsFn(e) == [
    label |-> "",
    color |-> IF e \in s2 /\ e \notin s1 THEN "blue" ELSE "black"
    \* fontsize |-> "8"
]

GraphElem == <<Group(<<DiGraph(Nodes,Edges,
                                   [n \in Nodes |-> nodeAttrsFn(n)], 
                                   [e \in Edges |-> edgeAttrsFn(e)])>>, 
                                   [transform |-> "translate(0, 10) scale(0.67)"])>>


\* 
\* Animation view.
\* 
AnimView == Group(GraphElem, [transform |-> "translate(60, 10) scale(1.7)"])



====
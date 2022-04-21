#lang forge

sig Node {
    edges : set Edge
}

sig Edge {
    weight : one Int,
    start: one Node,
    end: one Node,
    // rank used as tiebreaker when finding lowest weight edge (a unique integer)
    rank: one Int
}

sig Graph {
    nodes : set Node,
    edges : set Edge
}

sig SpanningTree {
    nodes : set Node,
    edges : set Edge
}

pred isRankUnique[graph: Graph] {
    all disj e1, e2: graph.edges | e1.rank != e2.rank
}

fun findLowestWeightEdge[graph: Graph] : Edge {
    {e1: graph.edges | no e2: graph.edges | e1 != e2 and e1.weight > e2.weight}
}

fun findCompetingLowestWeightEdge[graph: Graph] : Edge {
    not one findLowestWeightEdge 
    implies {e1: graph.edges | no e2: graph.edges | e1 != e2 and e1.weight > e2.weight and e1.rank < e2.rank} 
    else findLowestWeightEdge
}

pred includesEveryVertex[graph: Graph, mst: SpanningTree] {
    all v: graph.nodes | some e: mst.edges | v = e.vertexOne or v = e.vertexTwo
}

pred noSelfLoops[graph: Graph] {
    no e: graph.edges | e.vertexOne = e.vertexTwo
}

pred isConnectedGraph[graph: Graph] {
    all e: graph.edges | e.vertexOne in graph.nodes and e.vertexTwo in graph.nodes
    all disj v1, v2: graph.nodes | v1 in v2.^(edges)
}

pred isAcyclicGraph[graph: Graph] {
    all e: graph.edges | e.vertexOne in graph.nodes and e.vertexTwo in graph.nodes
    all v: graph.nodes | v not in v.^(edges)
}

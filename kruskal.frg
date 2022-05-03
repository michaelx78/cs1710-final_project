#lang forge

sig Vertex {
    neighbors: set Edge
}

sig Edge {
    endpoint_one: one Vertex,
    endpoint_two: one Vertex,
    // relation: set Vertex -> Vertex,
    weight: one Int
    // next: lone Edge
}

one sig Graph {
    vertices: set Vertex,
    edges: set Edge
}

// sig SpanningTree {
//     mst_vertices: set Vertex,
//     mst_edges: set Edge
// }

// pred isRankUnique[graph: Graph] {
//     all disj e1, e2: graph.edges | e1.rank != e2.rank
// }

// fun findLowestWeightEdge[graph: Graph] : Edge {
//     {e1: graph.edges | no e2: graph.edges | e1 != e2 and e1.weight > e2.weight}
// }

// fun findCompetingLowestWeightEdge[graph: Graph] : Edge {
//     not one findLowestWeightEdge 
//     implies {e1: graph.edges | no e2: graph.edges | e1 != e2 and e1.weight > e2.weight and e1.rank < e2.rank} 
//     else findLowestWeightEdge
// }

// pred includesEveryVertex[graph: Graph, mst: SpanningTree] {
//     all v: graph.nodes | some e: mst.edges | v = e.vertexOne or v = e.vertexTwo
// }

pred allVerticesInGraph {
    all v: Vertex | v in Graph.vertices
}

pred allEdgesInGraph {
    all e: Edge | e in Graph.edges
}

pred noSelfLoops {
    all e: Graph.edges | e.endpoint_one != e.endpoint_two
}

// pred isConnectedGraph[graph: Graph] {
//     all e: graph.edges | e.vertexOne in graph.nodes and e.vertexTwo in graph.nodes
//     all disj v1, v2: graph.nodes | v1 in v2.^(edges)
// }

// pred isAcyclicGraph[graph: Graph] {
//     all e: graph.edges | e.vertexOne in graph.nodes and e.vertexTwo in graph.nodes
//     all v: graph.nodes | v not in v.^(edges)
// }

run {
    allVerticesInGraph
    allEdgesInGraph
    noSelfLoops
} for exactly 3 Vertex, exactly 3 Edge

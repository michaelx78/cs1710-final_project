#lang forge

// sig that models graph data structure by having Node -> Node -> Int relation,
// where Int refers to the edge weight
sig Node {
    edges: set Node -> Int
}

// ensures that there are no self loops
// in other words, non-reflexive
pred noSelfLoops {
    all n: Node | no edges[n][n]
}

// ensures that there can be at most one edge directed from one Node to 
// another Node
pred atMostOneEdgeBetweenNodes {
    all n1, n2: Node | lone edges[n1][n2]
}

// ensures that edge weights are positive
pred positiveEdgeWeights {
    all n1, n2: Node | {
        some edges[n1][n2] implies
        edges[n1][n2] > 0
    }
}

// ensures that edge weights are unique
// with this condition, there is only one minimum spanning tree
pred uniqueEdgeWeights {
    // for any two edges, if their edge weights are equal, they either refer to
    // the same edge or the oppositely directed edge
    all n1, n2, n3, n4: Node | {
        (some edges[n1][n2] and some edges[n3][n4] and edges[n1][n2] = edges[n3][n4]) implies
        ((n1 = n3 and n2 = n4) or (n1 = n4 and n2 = n3))
    }
}

// safegaurd so that total weight of all edges is below max Int threshold
// constrains types of graphs that can be produced
pred maximumEdgeWeights {
     all n1, n2: Node | {
        some edges[n1][n2] implies {
            edges[n1][n2] < divide[max[Int],divide[#{edges},2]] 
        }
    }
}

// ensures that the graph is connected
// all nodes should be reachable from all other nodes
// with this condition, it finds a minimum spanning tree, not a minimum
// spanning forest
pred connectedGraph {
    all disj n1, n2: Node | n1 in n2.^(edges.Int)
}

// creates a graph that is complete
// in other words, each node has an edge to every other node
// in a complete graph, the number of edges is equal to the N * (N - 1), where
// N is the number of nodes
pred completeGraph {
    #{edges} = multiply[#{Node}, subtract[#{Node}, 1]]
}

// ensures that the graph is undirected
// in other words, that it is symmetric
pred undirectedGraph {
    all n1, n2: Node | edges[n1][n2] = edges[n2][n1]
}

// well formed conditions to produce a valid graph
pred wellFormed {
    noSelfLoops
    atMostOneEdgeBetweenNodes
    positiveEdgeWeights
    uniqueEdgeWeights
    // maximumEdgeWeights // uncomment to prevent total Int from wrapping around
    connectedGraph
    // completeGraph // uncomment if you want to see Kruskal's Algorithm run on a complete graph
    undirectedGraph
}

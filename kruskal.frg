#lang forge

sig Node {
    edge: set Node -> Int
}

pred noSelfLoops {
    no (iden & edge.Int)
}

pred atMostOneEdgeBetweenNodes {
    all n1, n2: Node | lone edge[n1][n2]
}

pred positiveEdgeWeights {
    all n1, n2: Node | {
        some edge[n1][n2] implies 
        edge[n1][n2] > 0
    }
}

pred uniqueEdgeWeights {
    all n1, n2, n3, n4: Node | {
        (some edge[n1][n2] and some edge[n3][n4] and edge[n1][n2] = edge[n3][n4]) implies
        ((n1 = n3 and n2 = n4) or (n1 = n4 and n2 = n3))
    }
}

pred connectedGraph {
    all disj n1, n2: Node | n1 in n2.^(edge.Int)
}

pred undirectedGraph {
    all n1, n2: Node | edge[n1][n2] = edge[n2][n1]
}

pred wellFormed {
    noSelfLoops
    atMostOneEdgeBetweenNodes
    positiveEdgeWeights
    uniqueEdgeWeights // for simplicity for now
    connectedGraph
    undirectedGraph
}

run {
    wellFormed
} for exactly 5 Node
 
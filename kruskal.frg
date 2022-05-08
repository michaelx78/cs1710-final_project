#lang forge

option problem_type temporal

sig Edge {
    weight: one Int,
    fromNode: one Node,
    toNode: one Node
}

sig Node {
    edge: set Node -> Int,
    var root: lone Node
}

sig Kruskal {
    nodes: set Node,
    tree: set Node->Node,
    edges: set Edge
    roots: pfunc Node -> set Node
}

one sig Unvisited  {
    possibleEdges: set Edge
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
    all n, m: Node | n.edges[m] = m.edges[n] -- symmetric
    
    noSelfLoops
    atMostOneEdgeBetweenNodes
    positiveEdgeWeights
    uniqueEdgeWeights // for simplicity for now
    connectedGraph
    undirectedGraph
}

pred noCycles[k: Kruskal, e : Edge] {
    e.fromNode not in k.nodes or e.toNode not in k.nodes
}

fun getLowestEdgeWeight[k : Kruskal]: Edge {
    {e1: Unvisited.possibleEdges | no e2: Unvisited.possibleEdges | 
        e1 != e2 and e1.weight > e2.weight and noCycles[k, e1] and e1 not in k.edges}
}


pred kruskal_init[k : Kruskal] {
    no k.nodes
    no k.tree

    noSelfLoops
    atMostOneEdgeBetweenNodes
    positiveEdgeWeights
    uniqueEdgeWeights // for simplicity for now
    connectedGraph
    undirectedGraph

    all e : Edges | {
        e in Unvisited.possibleEdges
    }
}

pred extend_kruskal[pre, post : Kruskal] {
    let lowestEdge = getLowestEdgeWeight[pre] | {
        Unvisited.possibleEdges' = Unvisited.possibleEdges - lowestEdge
        //add edge 
        post.tree = pre.tree + (lowestEdge.fromNode -> lowestEdge.toNode) + (lowestEdge.toNode -> lowestEdge.fromNode)
        post.edges = pre.edges + lowestEdge
        post.nodes = pre.nodes + lowestEdge.fromNode + lowestEdge.toNode
        //union if possible
    }
}

// pred kruskal_transition[pre, post : Kruskal] {
//     //get edge
//     let lowestEdge = getLowestEdgeWeight[pre] | {
//         //get edge
//         //check if edge creates cycle
//         Unvisited.possibleEdges' = Unvisited.possibleEdges - lowestEdge
//         //add edge 
//         post.tree = pre.tree + (lowestEdge.fromNode -> lowestEdge.toNode) + (lowestEdge.toNode -> lowestEdge.fromNode)
//         post.edges = pre.edges + lowestEdge
//         post.nodes = pre.nodes + lowestEdge.fromNode + lowestEdge.toNode
//         //union if possible

//         // both nodes have no root
//         (no lowestEdge.fromNode.root and no lowestEdge.toNode.root) implies {
//             lowestEdge.fromNode.root' = lowestEdge.fromNode and
//             lowestEdge.toNode.root' = lowestEdge.fromNode
//         }
//         //fromNode has root, toNode has no root
//         (one lowestEdge.fromNode.root and no lowestEdge.toNode.root) implies {
//             lowestEdge.toNode.root' = lowestEdge.fromNode.root
//         }
//         //fromNode has no root, toNode has root
//         (no lowestEdge.fromNode.root and one lowestEdge.toNode.root) implies {

//         }
//         //both have root
//         (one lowestEdge.fromNode.root and one lowestEdge.toNode.root 
//             and not lowestEdge.fromNode.root = lowestEdge.toNode.root) implies {
//             //overwrite all root fields for multiple nodes
//         }
//     }

// }

pred kruskal_final[k : Kruskal] {
    all disj n1, n2: Node | n1 in n2.^(k.tree)
}



run {
    wellFormed
} for exactly 5 Node
 
// for finding lowest weight edge, maybe store edge weights as linkedlist?
// maybe have an inherent ordering of the edges to save time, maybe not needed
// using Forge set operations can help with union-find
//consider model testing a bit more, verifications of something like MSTs


// should we ask Megan abt adding the graph as a parameter
// for the preds
// which Forge set opertions to use?
// use the visualizer
// if there's unique edges, there's only 1 MST

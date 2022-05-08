#lang forge

sig Node {
    edges: set Node -> Int
}

pred noSelfLoops {
    all n: Node | no edges[n][n]
}

pred atMostOneEdgeBetweenNodes {
    all n1, n2: Node | lone edges[n1][n2]
}

pred positiveEdgeWeights {
    all n1, n2: Node | {
        some edges[n1][n2] implies
        edges[n1][n2] > 0
    }
}

pred uniqueEdgeWeights {
    all n1, n2, n3, n4: Node | {
        (some edges[n1][n2] and some edges[n3][n4] and edges[n1][n2] = edges[n3][n4]) implies
        ((n1 = n3 and n2 = n4) or (n1 = n4 and n2 = n3))
    }
}

pred maximumEdgeWeights {
     all n1, n2: Node | {
        some edges[n1][n2] implies 
        edges[n1][n2] < divide[max[Int], divide[#{edges}, 2]]
    }
}

pred connectedGraph {
    all disj n1, n2: Node | n1 in n2.^(edges.Int)
}

pred completeGraph {
    #{edges} = multiply[#{Node}, subtract[#{Node}, 1]]
}

pred undirectedGraph {
    all n1, n2: Node | edges[n1][n2] = edges[n2][n1]
}

pred wellFormed {
    noSelfLoops
    atMostOneEdgeBetweenNodes
    positiveEdgeWeights
    uniqueEdgeWeights // for simplicity for now
    // maximumEdgeWeights
    connectedGraph
    // completeGraph
    undirectedGraph
}

sig KruskalsAlgorithmState {
    parents: set Node -> Node,
    ranks: set Node -> Int,
    used: set Node -> Node,
    remaining: set Node -> Node -> Int,
    total: one Int,
    next: lone KruskalsAlgorithmState
}

fun minimumEdgeWeight[e: set Node -> Node -> Int]: Int {
    min[e[Node][Node]]
}

fun findRoot[n: Node, s: KruskalsAlgorithmState]: Node {
    {n1: Node | n1 in n.*(s.parents) and s.parents[n1] = n1}
}

pred unionFind[n1: Node, n2: Node, n1Root: Node, n2Root: Node, pre: State, post: State] {
    pre.ranks[n1Root] < pre.ranks[n2Root] implies {
        post.parents[n1Root] = n2Root
        all n: n1.^(pre.parents) - n1Root | post.parents[n] = n1Root
        all n: n2.^(pre.parents) | post.parents[n] = n2Root
        all n: {Node - n1.^(pre.parents) - n2.^(pre.parents) - n1Root - n2Root} | post.parents[n] = pre.parents[n]
        post.ranks = pre.ranks
    } else {
        pre.ranks[n1Root] > pre.ranks[n2Root] implies {
            post.parents[n2Root] = n1Root
            all n: n1.^(pre.parents) | post.parents[n] = n1Root
            all n: n2.^(pre.parents) - n2Root | post.parents[n] = n2Root
            all n: {Node - n1.^(pre.parents) - n2.^(pre.parents) - n1Root - n2Root} | post.parents[n] = pre.parents[n]
            post.ranks = pre.ranks
        } else {
            post.parents[n1Root] = n2Root
            all n: n1.^(pre.parents) - n1Root | post.parents[n] = n1Root
            all n: n2.^(pre.parents) | post.parents[n] = n2Root
            all n: {Node - n1.^(pre.parents) - n2.^(pre.parents) - n1Root - n2Root} | post.parents[n] = pre.parents[n]
            post.ranks = pre.ranks - (n2Root->pre.ranks[n2Root]) + (n2Root->add[pre.ranks[n2Root], 1])
        }
    }
}

pred initialState[s: KruskalsAlgorithmState] {
    all n: Node | s.parents[n] = n
    all n: Node | s.ranks[n] = 0
    no s.used
    s.remaining = edges
    s.total = 0
}

pred canTransition[pre: KruskalsAlgorithmState, post: KruskalsAlgorithmState] {
    let minimumEdgeWeight = minimumEdgeWeight[pre.remaining] |
    let minimumEdge = pre.remaining.minimumEdgeWeight |
    some disj n1, n2: Node | {
        n1 in minimumEdge.Node
        n2 in minimumEdge.Node
        post.remaining = pre.remaining - (n1->n2->minimumEdgeWeight) - (n2->n1->minimumEdgeWeight)
        let n1Root = findRoot[n1, pre] |
        let n2Root = findRoot[n2, pre] |
        n1Root != n2Root implies {
            post.used = pre.used + (n1->n2) + (n2->n1)
            post.total = add[pre.total, minimumEdgeWeight]
            unionFind[n1, n2, n1Root, n2Root, pre, post]
        } else {
            post.parents = pre.parents
            post.ranks = pre.ranks
            post.used = pre.used
            post.total = pre.total
        }
    }
}

pred finalState[s: KruskalsAlgorithmState] {
    divide[#{s.used}, 2] = subtract[#{Node}, 1]
}

pred fullTrace {
    some disj i, f: KruskalsAlgorithmState {
        initialState[i]
        finalState[f]
        no s: KruskalsAlgorithmState | {
            s.next = i
        }
        no f.next
    }
    all s: KruskalsAlgorithmState | {
        some s.next => canTransition[s, s.next]
    }
}

pred doesTreeSpan {
    fullTrace implies {
        some st : KruskalsAlgorithmState | {
            all disj n1, n2: Node | {
                n1 not in n2.^(st.used)
            }
        }
    }
}

pred noLowerWeightMST {
    // no disj s1, s2 :  KruskalsAlgorithmState | {
    //     finalState[s1] and finalState[s2]
    // }
    some finalSt: KruskalsAlgorithmState | {
        finalState[finalSt]
        no otherSt: KruskalsAlgorithmState | {
            finalState[otherSt] and otherSt.total < finalSt.total
        }
    } 
}

run {
    wellFormed
    fullTrace
} for exactly 4 Node, 5 Int for {next is linear} // does not work for exactly 5+ Node? (unsure if because of code or limitations of Forge)

test expect {
    reachAllNodesTest: {doesTreeSpan} for exactly 4 Node, 5 Int is theorem
    noOtherMSTTest: {noLowerWeightMST} for exactly 4 Node, 5 Int is sat
}
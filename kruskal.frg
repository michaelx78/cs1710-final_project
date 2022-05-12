#lang forge

open "graph.frg"

// sig that maintains track of a state in Kruskal's Algorithm
// we implement Kruskal's Algorithm using the union find algorithm but
// optimizations with find and compression and union by rank
sig KruskalsAlgorithmState {
    parents: set Node -> Node,
    ranks: set Node -> Int,
    used: set Node -> Node,
    remaining: set Node -> Node -> Int,
    total: one Int,
    next: lone KruskalsAlgorithmState
}

// function that finds the minimum edge weight
fun minimumEdgeWeight[e: set Node -> Node -> Int]: Int {
    min[e[Node][Node]]
}

// function that returns the node reachable from the parents relation and whose
// parent equals itself
fun findRoot[n: Node, s: KruskalsAlgorithmState]: Node {
    {n1: Node | n1 in n.*(s.parents) and s.parents[n1] = n1}
}


// core of the union find algorithm
pred unionFind[n1: Node, n2: Node, n1Root: Node, n2Root: Node, pre: State, post: State] {
    // if rank of n1Root is less than rank of n2Root
    pre.ranks[n1Root] < pre.ranks[n2Root] implies {
        // change parent of n1Root to be n2Root
        post.parents[n1Root] = n2Root
        // all nodes reachable from n1 (not including n1Root) will have parents equal to n1Root
        all n: n1.^(pre.parents) - n1Root | post.parents[n] = n1Root
        // all nodes reachable from n2 will have parents equal to n2Root
        all n: n2.^(pre.parents) | post.parents[n] = n2Root
        // all other nodes' parents will remain the same in the post state
        all n: {Node - n1.^(pre.parents) - n2.^(pre.parents) - n1Root - n2Root} | post.parents[n] = pre.parents[n]
        // ranks will remain the same
        post.ranks = pre.ranks
    } else {
        // if rank of n1Root is greater than rank of n2Root
        pre.ranks[n1Root] > pre.ranks[n2Root] implies {
            // change parent of n2Root to be n1Root
            post.parents[n2Root] = n1Root
            // all nodes reachable from n1 will have parents equal to n1Root
            all n: n1.^(pre.parents) | post.parents[n] = n1Root
            // all nodes reachable from n2 (not including n2Root) will have parents equal to n2Root
            all n: n2.^(pre.parents) - n2Root | post.parents[n] = n2Root
            // all other nodes' parents will remain the same in the post state
            all n: {Node - n1.^(pre.parents) - n2.^(pre.parents) - n1Root - n2Root} | post.parents[n] = pre.parents[n]
            // ranks will remain the same
            post.ranks = pre.ranks
        } else {
            // if rank of n1Root is less than rank of n2Root
            // this is arbitrarily chosen
            post.parents[n1Root] = n2Root
            // all nodes reachable from n1 (not including n1Root) will have parents equal to n1Root
            all n: n1.^(pre.parents) - n1Root | post.parents[n] = n1Root
            // all nodes reachable from n2 will have parents equal to n2Root
            all n: n2.^(pre.parents) | post.parents[n] = n2Root
            // all other nodes' parents will remain the same in the post state
            all n: {Node - n1.^(pre.parents) - n2.^(pre.parents) - n1Root - n2Root} | post.parents[n] = pre.parents[n]
            // rank of n2Root will increment by one
            // ranks of other nodes will remain the same
            post.ranks = pre.ranks - (n2Root->pre.ranks[n2Root]) + (n2Root->add[pre.ranks[n2Root], 1])
        }
    }
}

// describes the initial state of Kruskal's Algorithm
pred initialState[s: KruskalsAlgorithmState] {
    all n: Node | s.parents[n] = n
    all n: Node | s.ranks[n] = 0
    no s.used
    s.remaining = edges
    s.total = 0
}

// describes whether or not you can transition between the pre state and post state
pred canTransition[pre: KruskalsAlgorithmState, post: KruskalsAlgorithmState] {
    // find minimum edge weight
    let minimumEdgeWeight = minimumEdgeWeight[pre.remaining] |
    // find associate edge
    let minimumEdge = pre.remaining.minimumEdgeWeight |
    some disj n1, n2: Node | {
        // find nodes involved with minimum edge
        n1 in minimumEdge.Node
        n2 in minimumEdge.Node
        // ensure we have not used this edge before
        n1 not in n2.^(pre.used)
        n2 not in n1.^(pre.used)
        // include this edge in the minimum spanning tree and remove it from the remaining edges
        post.remaining = pre.remaining - (n1->n2->minimumEdgeWeight) - (n2->n1->minimumEdgeWeight)
        // find the roots of n1 and n2
        let n1Root = findRoot[n1, pre] |
        let n2Root = findRoot[n2, pre] |
        // if they do not equal, they do not belong to the same disjoint set
        // update edges used in the minimum spanning tree and its total weight thus far
        // perform union find algorithm
        n1Root != n2Root implies {
            post.used = pre.used + (n1->n2) + (n2->n1)
            post.total = add[pre.total, minimumEdgeWeight]
            unionFind[n1, n2, n1Root, n2Root, pre, post]
        } else {
            // otherwise, the pre state and post state should remain the same
            post.parents = pre.parents
            post.ranks = pre.ranks
            post.used = pre.used
            post.total = pre.total
        }
    }
}

// describes the final state of Kruskal's Algorithm
// a minimum spanning tree should reach every vertex,
// so the number of undirected used edges should equal
// the number of Nodes minus one
pred finalState[s: KruskalsAlgorithmState] {
    divide[#{s.used}, 2] = subtract[#{Node}, 1]
}

// generates a full trace of Kruskal's Algorithm
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

// run command that runs for a graph with exactly four Nodes
run {
    wellFormed
    fullTrace
} for exactly 4 Node, 5 Int for {next is linear}

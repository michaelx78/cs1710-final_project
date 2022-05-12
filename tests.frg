#lang forge

open "graph.frg"
open "kruskal.frg"

// ensures that the tree does span
// in other words, includes all nodes
pred doesTreeSpan {
    wellFormed
    fullTrace implies {
        some st : KruskalsAlgorithmState | {
            all disj n1, n2: Node | {
                n1 in n2.^(st.used)
            }
        }
    }
}

// ensure that there is no other minimum spanning tree with a lower weight
pred noLowerWeightMST {
    wellFormed
    some finalSt: KruskalsAlgorithmState | {
        finalState[finalSt]
        no otherSt: KruskalsAlgorithmState | {
            finalState[otherSt] and otherSt.total < finalSt.total
        }
    } 
}

// ensures that the result minimum spanning tree has no cycles
pred noCycles {
    wellFormed
    all st :  KruskalsAlgorithmState | {
        all n: Node {
            some n->n.edges.Int & st.used
            no disj n1, n2: Node | {
                n1 = n
                n2 = n
                n->n1 in st.used and n2->n in st.used
                n1 in n2.^(st.used)
            }
        }
    }
}

// tests the above conditions
test expect {
    reachAllNodesTest: {doesTreeSpan} for exactly 4 Node, 5 Int is sat
    noOtherMSTTest: {noLowerWeightMST} for exactly 4 Node, 5 Int is sat
    noCyclesTest: {noCycles} for exactly 4 Node, 5 Int is sat
}

# README

We have modeled Kruskal's Algorithm, a greedy approach to finding a minimum spanning tree (MST) for an undirected edge-weighted graph. The main idea of Kruskal's is to build a MST by 
identifying and choosing the lowest-cost edges that have not been used.

## Implementation

Our modeling of an undirected edge-weighted graph is based upon the Prim's algorithm model shared by Tim, which represented this type of graph with only a Node sig. The Node sig has an *edges* field, a set of Node->Int binary relations representing edges stemming from a Node.
We include several predicates for a well-formed graph, such as ensuring the graph is undirected and has positive edge weights.

For Kruskal's algorithm, we created a KruskalsAlgorithmState sig. This sig has a *used* and *remaining* fields, both are sets containing the edges used and unused in the building of the MST, respectively. We also have *parents* and *rank* fields for our union-by-rank implementation (discussed below).

To find a MST using Kruskal's, we use a trace approach where each KruskalsAlgorithmState instance represents a unique time-step in the MST's creation. Thus, we define an initial state and a final state, that the final state tree has 1 more node than the number of edges.

## Assumptions

In building this model, we started off by defining edges with unique edge weights. If all edges have unique edge weights, only one MST exists. This property helped us build and test an initial model for Kruskal's. Due to Int overflow concerns, we also build the capacity for the model to work on edges with similar weights.

### Union by Rank

To stay true to Kruskal's algorithm, we decided to implement union by rank. We did this because building smaller sub-trees and merging sub-trees is the basis of Kruskal's algorithm.

Union by rank is based upon the disjoint set data structure, which is the core of Kruskal's. Essentially, if we wish to join two sub-treesto create a larger tree, the sub-tree with less nodes should merge into the larger sub-tree for higher efficiency. This method and path compression are implemented into our model to represented an optimized model of Kruskal's

[This article](https://medium.com/@harshits337/disjoint-set-unions-by-rank-and-path-compression-3a7b3946f550) provides more insight into union by rank and path compression.

## Testing
Our testing checks to see if the tree build by the model is a MST. 

When the **uniqueEdgeWeights** predicate is activated (i.e. not commented out), there should only be 1 MST for the given graph, so the **noLowerWeightMST** predicate ensures this is the case. We also have tests to check if the tree found spans across all nodes and if the tree has no cycles in it, all to verify the tree as a MST.

Our current github commit has sat tests. A prior commit (titled "README v2", commit id a268269) has theorem tests in the kruskal.frg file. We wanted to seperate the large kruskal.frg into smaller files and we needed to switch to "sat" to pass the tests.

## Limitations

At first, we started off with our reach goal being to model out Kruskal's variations from research papers. This was suggested by our 3rd team member, who stepped away from this final project. The 2 remaining members had less familiarity than the 3rd member with Kruskal's, so the target goal became to properly model Kruskal's, hopefully with the union by rank optimization.

After scaling back our project, we were able to finish it. There are limitations within our model however...

## Bugs

Yeah, we have bugs :(

Our model does not work with 5 or more nodes; it results in a "unsat". 'Tis a shame. 

We were advised by Tim and Megan that our error may have to do with an int overflow error from adding and finding the total of a tree's weights. We put several constraints to ensure int overflow never occurs, like ensuring the total of a tree's weights never reaches max[Int]. Alas, the "unsat" persists.

Our model does work for 4 or fewer nodes. This stifled our debugging because we were unsure why the model worked fine for 4 or fewer nodes, but broke after adding a 5th node. We are unsure what causes the "unsat".

## Acknowledgements

Thanks to Tim and Megan for their guidance during this project!
Our model is inspired by the [Prim's algorithm model](https://hackmd.io/@lfs/rk27CaIN9) Tim has shared in Lecture 31.


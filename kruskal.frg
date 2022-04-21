#lang forge

sig Edge {
    weight : one Int,
    start: one Node,
    end: one Node
}

sig Node {
    edges : set Edge
}

sig SpanningTree {
    nodes : set Node
}


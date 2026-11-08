<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/DirectedWalk.lean :: Randomized.chainDigraph_reachable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability in a Chain Digraph

**Claim.** In the directed graph on $\{0,1,\ldots,n\}$ with an edge from $i$ to $j$ whenever $j=0$ or $j=i+1$, there is a directed path from $0$ to $n$, allowing a path of length zero.

**Proof.** Prove by induction on $i$ that every vertex $i$ with $i<n+1$ is reachable from $0$. The base case $i=0$ is the path of length zero. For the successor step, a path to $i$ extends by one edge to $i+1$, since the graph contains the edge from $i$ to $i+1$. Taking $i=n$ gives reachability of the last vertex.

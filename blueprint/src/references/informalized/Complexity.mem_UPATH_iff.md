<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPath.lean :: Complexity.mem_UPATH_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding characterization of undirected path reachability

**Claim.** A string belongs to the encoded undirected path language exactly when it has the prescribed unary, adjacency-matrix, and endpoint format, its encoded adjacency relation is symmetric, and its designated vertices are connected by a path.

**Proof.** Suppose first that $x$ is the encoding of a graph with adjacency function $A$ and designated vertices $s,t$, and that $A$ is symmetric with a path from $s$ to $t$. The encoding-format lemma (ushape_of_eq) supplies the required shape conditions and identifies each decoded edge with the corresponding value of $A$. Applying that identification in both directions transfers symmetry of $A$ to symmetry of the decoded edge relation. It also transfers every edge of the given path, so the path remains a path in the decoded relation.

Conversely, suppose $x$ satisfies the shape conditions and the decoded edge relation is symmetric, with a path between the designated vertices. The converse format lemma (exists_eq_of_ushape) constructs an adjacency function $A$ whose graph encoding is exactly $x$ and whose true edges are exactly the decoded edges. The assumed symmetry of the decoded relation implies symmetry of $A$: for each pair of vertices, the two edge indicators agree. Translating each edge along the given path through the same identification gives a path in $A$. Thus $x$ is an encoding of a symmetric graph with the required reachability.

**Key facts.** `Complexity.ushape_of_eq`, `Complexity.exists_eq_of_ushape`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean :: Complexity.pathAcc_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Path encoding characterization

**Claim.** A binary string satisfies the stated path-encoding conditions exactly when it is a raw encoding of a finite directed graph with designated source and target, with the target reachable from the source.

**Proof.** For the forward direction, start with the unary, matrix, vertex, and walk data in the path-encoding conditions. The matrix-tail characterization (`Complexity.matRest_iff`) supplies a list $M$ of length $n^2$ whose doubled encoding occupies the specified matrix segment. The unary characterization (`Complexity.unaryRest_iff`) identifies the initial segment with the doubled unary encoding of $n$. The layout equivalence `Complexity.eq_pathRaw_iff` then shows that the whole string is `pathRaw n M s t`. To transfer the walk, note that for $u,v<n$, row-major indexing gives $un+v<n^2$ (`Complexity.rowMajor_lt`); the doubled matrix encoding therefore makes the encoded edge condition equivalent to $M[un+v]=1$. The equivalence between bounded walks and reflexive transitive reachability (`Complexity.reach_iff_walkLe`) converts the given walk into reachability in the graph described by $M$.

Conversely, suppose the string is a raw encoding with matrix $M$ of length $n^2$ and with a path from $s$ to $t$. The layout equivalence recovers the unary, matrix, and vertex-segment conditions; replace the matrix length by $n^2$ to match their stated offsets. The unary and matrix-tail characterizations give the required unary-rest and matrix-rest conditions. Convert the path to a bounded walk using `Complexity.reach_iff_walkLe`. For each graph edge, its row-major matrix entry is true, and the doubled encoding makes the corresponding path-edge bit true by the same indexing observation. This gives all the conditions in `PathAcc`.

**Key facts.** `Complexity.matRest_iff`, `Complexity.unaryRest_iff`, `Complexity.eq_pathRaw_iff`, `Complexity.rowMajor_lt`, `Complexity.reach_iff_walkLe`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPath.lean :: Complexity.ushape_of_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shape and Edges of an Encoded Path Instance

**Claim.** If $x$ is the prescribed nested self-delimiting encoding determined by $n$, the Boolean relation $A$, and endpoints $s,t$, then $x$ has the specified unary, matrix, and endpoint shape; moreover, each encoded path edge at indices $u,v<n$ holds exactly when $A(u,v)$ is true.

**Proof.** First, the encoding equality gives the four componentwise delimiter and content conditions for the raw path encoding, by `eq_pathRaw_iff`. The row-major adjacency list has length $n^2$ (`length_adjWord`), so substituting this length identifies the matrix block's start and its delimiter; the matrix-shape characterization `matRest_iff` then gives the required matrix condition. The unary-block characterization `unaryRest_iff` supplies the unary condition. The endpoint bounds $s<n$ and $t<n$ follow because $s,t$ are elements of `Fin n`; the delimiter and content conditions for their binary expansions are the remaining clauses from the raw encoding characterization. Finally, for any $u,v<n$, the index $un+v$ lies below $n^2$ (`rowMajor_lt`). The matrix-block condition therefore identifies the encoded bit at that row-major position with the corresponding entry in the adjacency list, and `adjWord_getD` identifies that list entry with $A(u,v)$. Hence the encoded edge bit is true exactly when $A(u,v)$ is true.

**Key facts.** `Complexity.length_adjWord`, `Complexity.eq_pathRaw_iff`, `Complexity.unaryRest_iff`, `Complexity.matRest_iff`, `Complexity.rowMajor_lt`, `Complexity.adjWord_getD`.

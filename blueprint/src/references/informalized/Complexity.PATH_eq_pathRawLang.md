<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean :: Complexity.PATH_eq_pathRawLang -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Path Encodings

**Claim.** A binary word encodes a reachable directed graph instance using the matrix encoding if and only if it encodes one using the raw-list encoding.

**Proof.** For a matrix-encoded instance $(n,A,s,t)$, the row-by-row adjacency word has length $n^2$, by `length_adjWord`. Its entry at position $u n+v$ is exactly $A(u,v)$, by `adjWord_getD`. Therefore the same word and vertices witness membership in the raw-list language: every matrix edge gives a raw edge, and lifting each step of the reachable path through the vertex-value map transfers reachability to natural-number vertices.

Conversely, suppose a raw-list witness $(n,M,s,t)$ has $n^2$ adjacency bits and a path from $s$ to $t$. Define the matrix by $A(u,v)=M.getD(un+v,\mathrm{false})$. The row-by-row adjacency word for this matrix has length $n^2$, again by `length_adjWord`. For each position $i<n^2$, divide $i$ by $n$ to write it as $(i/n)n+(i\bmod n)$; both quotient and remainder are less than $n$. The identity `adjWord_getD` then shows that the adjacency word and $M$ agree at that position. The list extensionality principle `ext_getD'` makes them equal, including the degenerate cases handled by the length condition. Consequently the two encodings coincide. Each raw edge in the given path is now a matrix edge, so induction over the reflexive-transitive path relation produces a matrix path between the corresponding finite vertices. This gives the matrix witness and proves the reverse inclusion.

**Key facts.** `Complexity.length_adjWord`, `Complexity.adjWord_getD`, `Complexity.ext_getD'`.

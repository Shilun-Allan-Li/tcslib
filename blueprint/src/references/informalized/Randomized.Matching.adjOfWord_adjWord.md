<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Matching.lean :: Randomized.Matching.adjOfWord_adjWord -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering a Matrix from Its Adjacency Word

**Claim.** For every Boolean matrix indexed by $\mathrm{Fin}(n)\times\mathrm{Fin}(n)$, decoding its adjacency word reconstructs the original matrix.

**Proof.** To prove equality of matrices, compare their entries at arbitrary indices $i,j\in\mathrm{Fin}(n)$. The decoded entry reads the adjacency word at position $i n+j$. The indexing lemma for adjacency words states that this position contains precisely the matrix entry $A_{ij}$ when $i,j<n$ (Randomized.Matching.getD_adjWord). Since the bounds hold for elements of $\mathrm{Fin}(n)$, the entries agree, hence the matrices are equal.

**Key facts.** `Randomized.Matching.getD_adjWord`.

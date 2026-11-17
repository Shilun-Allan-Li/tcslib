<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetModMath.lean :: Complexity.BinArith.matOfRows_map_mod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matrix Invariance Under Reduction

**Claim.** Reducing every entry of the row list modulo $p$ before constructing the matrix over $\mathbb Z/p\mathbb Z$ leaves the resulting matrix unchanged.

**Proof.** Compare the matrices entry by entry. At row index $i$, the row selected from the mapped list is the modulo-$p$ image of the row selected from the original list; if the selected row is missing, both selections give the empty list. Likewise, selecting column $j$ from a row commutes with mapping modulo $p$, with missing entries represented by zero. That default zero is unchanged by reduction modulo $p$, and casting a natural number reduced modulo $p$ into $\mathbb Z/p\mathbb Z$ agrees with casting the original number. Hence the two matrices have equal entries at every pair of indices.

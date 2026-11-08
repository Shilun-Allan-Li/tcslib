<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetModMath.lean :: Complexity.BinArith.getD_zipWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexing a Pointwise List Combination

**Claim.** If $j$ is less than the length of each of $l_1,l_2$, then the element at index $j$ of their pointwise combination under $f$, with default $0$, is $f$ applied to their respective elements at index $j$, each read with default $0$.

**Proof.** The length hypotheses ensure that the entries at index $j$ exist in both input lists and in their pointwise combination. Replacing each defaulted lookup by that existing entry, the indexed-entry rule for `zipWith` identifies the combined entry with $f$ of the two input entries. Reinstating the defaulted lookup notation gives the stated equality.

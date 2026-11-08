<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.encMat_eq_nil_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# When the Matrix Encoding Is Empty

**Claim.** For every list $R$ of lists of natural numbers, the encoding of $R$ as a matrix is empty if and only if $R$ is empty.

**Proof.** If $R$ is empty, its image under the map to encoded rows is empty, so flattening that list gives the empty bit string. Conversely, if $R$ has the form $r :: R'$, its encoding begins with the pair encoding of the bit string for the row $r$. Every pair encoding contains the delimiter $[0,1]$, so this first contribution is nonempty; consequently the full flattened encoding cannot be empty. Thus an empty matrix encoding forces $R$ itself to be empty.

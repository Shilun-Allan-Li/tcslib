<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterSteps.lean :: Complexity.UTab.range_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Range Partitioned into Blocks

**Claim.** For natural numbers $a$ and $S$, the range $[0,1,\ldots,aS-1]$ is the concatenation, in order of $t=0,1,\ldots,a-1$, of the ranges beginning at $tS$ and having length $S$.

**Proof.** We induct on the number $a$ of blocks. When $a=0$, both sides are empty. For the successor case, split the range of length $(a+1)S=aS+S$ into its initial segment of length $aS$ and its final segment of length $S$. By the induction hypothesis, the initial segment is the concatenation of the first $a$ blocks. The range of block indices for $a+1$ consists of those first $a$ indices followed by $a$; distributing the concatenation over this split leaves the final block as the range beginning at $aS$. Finally, the identity expressing a shifted range as the image of an ordinary range under addition ( `Complexity.UTab.range'_eq_map`) identifies this final segment with the required shifted block.

**Key facts.** `Complexity.UTab.range'_eq_map`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/BooleanCharacteristic.lean :: BooleanAnalysis.GaussianSpace.phase_normalizedCubeBlocks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Phase identity for normalized cube blocks

**Claim.** The weighted sum of the normalized sign sums over the blocks equals the sum over all coordinates of the corresponding block weights times their signs.

**Proof.** Reindex the sum over coordinates of length $nm$ by the equivalence between a coordinate and a pair $(i,j)$, with $i$ the block and $j$ the position within that block. The resulting sum is over all pairs. For each fixed block $i$, substitute the definition of its normalized sign sum. Distribute the factor $1/\sqrt m$ over the inner sum and distribute addition over the sum in $j$. Each summand then consists of the $a_i$-weighted sign from $x$ plus the $b_i$-weighted sign from $y$, divided by $\sqrt m$. Reindexing back from pairs to coordinates gives the displayed identity.

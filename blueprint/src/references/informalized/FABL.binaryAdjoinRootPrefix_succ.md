<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryAdjoinRootPrefix_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive root-power prefixes

**Claim.** The root-power sum through index $r$ is the sum through index $r-1$ together with the term at index $r$, using zero coefficients for indices beyond the vector's length.

**Proof.** The prefix with endpoint $r+1$ sums the terms indexed by $0\le i<r+1$. This range consists of the indices below $r$, together with the single index $r$. Splitting off that final term gives the prefix ending at $r$ plus the coefficient at index $r$ times the $r$th power of the adjoined root; the coefficient-at-index convention supplies zero when $r\ge\ell$.

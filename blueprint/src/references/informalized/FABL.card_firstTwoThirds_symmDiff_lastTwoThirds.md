<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/Examples.lean :: FABL.card_firstTwoThirds_symmDiff_lastTwoThirds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetric difference of index sets

**Claim.** For every positive natural number $m$, the symmetric difference of the first $2m$ indices and the last $2m$ indices among $3m$ indices has cardinality $2m$.

**Proof.** The first set contains the indices below $2m$, and the last set contains those at least $m$. Their symmetric difference consists precisely of indices below $m$ or at least $2m$. These two intervals are disjoint: an index cannot be both below $m$ and at least $2m$. Each interval has cardinality $m$, since the ambient index range is from $0$ to $3m-1$. Therefore their union, and hence the symmetric difference, has cardinality $m+m=2m$.

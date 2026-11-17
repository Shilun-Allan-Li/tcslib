<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityNoiseStability.lean :: FABL.fourierWeightAtLevel_eq_zero_of_dimension_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing above the dimension

**Claim.** If $k>n$, the Fourier weight of $f$ at level $k$ is zero.

**Proof.** The level-$k$ weight sums over subsets of an $n$-element set having cardinality $k$. Every such subset has cardinality at most $n$, which contradicts $k>n$. The indexing family is therefore empty, and its sum is zero.

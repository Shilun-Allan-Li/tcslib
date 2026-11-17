<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/FunctionsAsMultilinearPolynomials.lean :: FABL.fourierCoeff_eq_int_mul_global_scale_of_card_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integral Fourier Granularity

**Claim.** If the real-valued sign function has Fourier degree at most $k$, with $1\le k$, then every coefficient indexed by a set of size at most $k$ is an integer multiple of $2(2^{-1})^k$.

**Proof.** Let $d=k-|S|$, and use strong induction on $d$, keeping the set $S$ general. Consider the sum of Fourier coefficients over all supersets of $S. The top-coefficient identity (`granularityRestrictionTopCoeff_eq_sum_supersets`) identifies this sum with the granularity restriction at $S`; the latter is an integer multiple of the claimed scale (`granularityRestrictionTopCoeff_eq_int_mul_global_scale`). Separate the term indexed by $S$ from the remaining strict supersets. For each remaining superset $U$, if $|U|>k$, its coefficient vanishes by the degree characterization (`fourierDegree_le_iff`). Otherwise $|U|\le k$, and strict containment gives $|U|>|S|$, hence $k-|U|<d$. The induction hypothesis therefore says that each such coefficient is an integer multiple of the same scale. Their finite sum is also an integer multiple of that scale. Subtracting this sum from the top-coefficient multiple shows that the coefficient at $S$ is itself an integer multiple, as required.

**Key facts.** `FABL.granularityRestrictionTopCoeff_eq_sum_supersets`, `FABL.granularityRestrictionTopCoeff_eq_int_mul_global_scale`, `FABL.fourierDegree_le_iff`.

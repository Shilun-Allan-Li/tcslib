<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/Examples.lean :: FABL.hasSmallInfluences_zero_iff_exists_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero influences characterize constants

**Claim.** All coordinate influences of a real-valued function on the sign cube are at most zero if and only if the function is constant.

**Proof.** Assume first that all influences are at most zero. The zero-regularity characterization says it suffices to show that every nonempty Fourier coefficient vanishes (`isFourierRegular_zero_iff_exists_const`). Fix such a set $S$, choose a coordinate $i\in S$, and use the equivalence between small influences and bounds on coordinate influences (`hasSmallInfluences_iff`). The influence at $i$ is therefore at most zero, while influence is nonnegative (`influence_nonneg`), so it equals zero. The influence is also the sum of the squared Fourier coefficients over sets containing $i$ (`influence_eq_sum_sq_fourierCoeff`). Since each summand is nonnegative, the particular summand for $S$ is at most this sum, hence at most zero. Thus the square of the coefficient on $S$ is zero, and that coefficient vanishes. The zero-regularity characterization now gives that the function is constant.

Conversely, a constant function has all stable influences at most zero (`const_hasSmallStableInfluences_zero_zero`); taking the stability parameter to be zero gives the required small-influence condition.

**Key facts.** `FABL.isFourierRegular_zero_iff_exists_const`, `FABL.hasSmallInfluences_iff`, `FABL.influence_nonneg`, `FABL.influence_eq_sum_sq_fourierCoeff`, `FABL.const_hasSmallStableInfluences_zero_zero`.

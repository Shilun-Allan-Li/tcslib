<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.lowDegreeOutsideInfluentialMass_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-degree mass outside influential coordinates

**Claim.** The low-degree Fourier mass on sets not contained in the coordinates of influence at least $\tau$ is bounded by $3^k\sqrt{\tau}$ times the total influence of the real-valued sign representation.

**Proof.** First, bound the mass in question by summing, over coordinates whose influence is below $\tau$, the low-degree Fourier mass on sets containing that coordinate (`lowDegreeOutsideInfluentialMass_le_sum_coordinateMass`). For each such coordinate, its low-degree mass is at most $3^k\sqrt{\tau}$ times its Boolean influence (`lowDegreeCoordinateMass_le_three_pow_mul_sqrt_threshold_mul_influence`). Summing these bounds gives a sum over the coordinates outside the influential set. Since each summand is nonnegative, enlarging that coordinate set to all coordinates can only increase the sum; nonnegativity follows by identifying Boolean influence with the real-valued influence (`booleanInfluence_eq_influence_toReal`) and using nonnegativity of influence (`influence_nonneg`). Finally, factor the common constant out of the full sum and identify the sum of influences with total influence. This yields the claimed bound.

**Key facts.** `FABL.lowDegreeOutsideInfluentialMass_le_sum_coordinateMass`, `FABL.lowDegreeCoordinateMass_le_three_pow_mul_sqrt_threshold_mul_influence`, `FABL.booleanInfluence_eq_influence_toReal`, `FABL.influence_nonneg`.

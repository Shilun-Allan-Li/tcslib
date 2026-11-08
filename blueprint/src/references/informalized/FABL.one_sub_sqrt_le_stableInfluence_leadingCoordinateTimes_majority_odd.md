<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/Examples.lean :: FABL.one_sub_sqrt_le_stableInfluence_leadingCoordinateTimes_majority_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Stable Influence Bound

**Claim.** For every natural number $m$ and every $0\leq\delta\leq1$, the stable influence at parameter $1-\delta$ of the leading coordinate of leading-coordinate times odd majority on $2m+1$ signs is at least $1-\sqrt{\delta}$.

**Proof.** If $\delta=0$, the Fourier coefficients of majority have squared sum one, so its stability curve at $1$ equals one (Parseval, `sum_sq_fourierCoeff_eq_one`). The stability curve is bounded above by the leading coordinate's stable influence (`stabilityCurve_le_stableInfluence_leadingCoordinateTimes`), giving the result. For $\delta>0$, the arcsine estimate gives $1-\sqrt{\delta}\leq (2/\pi)\arcsin(1-\delta)$ (`one_sub_sqrt_le_two_div_pi_mul_arcsin_one_sub`). The odd-majority noise-stability lower bound shows that this is at most the noise stability of majority at $1-\delta$ (`two_div_pi_mul_arcsin_le_noiseStability_majority_odd`). This noise stability equals its stability curve (`stabilityCurve_eq_noiseStability`), which is again bounded above by the stable influence in question. The interval hypotheses needed for these comparisons follow from $0<\delta\leq1$.

**Key facts.** `FABL.sum_sq_fourierCoeff_eq_one`, `FABL.stabilityCurve_le_stableInfluence_leadingCoordinateTimes`, `FABL.one_sub_sqrt_le_two_div_pi_mul_arcsin_one_sub`, `FABL.two_div_pi_mul_arcsin_le_noiseStability_majority_odd`, `FABL.stabilityCurve_eq_noiseStability`.

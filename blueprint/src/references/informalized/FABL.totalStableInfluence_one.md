<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/StableInfluence.lean :: FABL.totalStableInfluence_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stable Influence at Unit Noise

**Claim.** At parameter $\rho=1$, total stable influence equals total influence.

**Proof.** Rewrite total stable influence as the sum over subsets $S$ of $|S|\,\rho^{|S|-1}\widehat f(S)^2$, and total influence as the sum of $|S|\widehat f(S)^2$. Setting $\rho=1$ makes the power factor equal to $1$ for every nonempty term; the empty-set term has coefficient $|S|=0$. Thus the sums agree.

**Key facts.** `FABL.totalStableInfluence_eq_sum_card_mul_rho_pow_mul_sq_fourierCoeff`, `FABL.totalInfluence_eq_sum_card_mul_sq_fourierCoeff`.

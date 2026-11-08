<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/BiasedMajorityGaussianLimit.lean :: FABL.tendsto_noiseStability_hammingUpperTailIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convergence of majority noise stability

**Claim.** For fixed threshold \(t\) and correlation \(\rho\in(-1,1)\), the noise stability of the threshold indicator of the normalized Rademacher sum converges to the correlated Gaussian probability of the corresponding upper-right quadrant.

**Proof.** First regard \(\rho\) as lying in the closed interval \([-1,1]\). The joint normalized correlated-sign sums converge in distribution to the correlated Gaussian pair; applying this convergence to the upper-right quadrant gives convergence of the associated probabilities (\(\texttt{normalizedCorrelatedSignSumMeasure_upperRight_tendsto}\)). Passing from nonnegative real probabilities to their real values preserves this limit. For each dimension, the probability of that quadrant is exactly the noise stability of the threshold indicator (\(\texttt{coe_normalizedCorrelatedSignSumMeasure_upperRight_eq_noiseStability}\)). Finally, the Gaussian upper quantile corresponding to the Gaussian upper-tail probability at \(t\) is \(t\) itself (\(\texttt{standardGaussianUpperQuantile_upperTailOpen_biasedMajority}\)); hence the limiting quadrant is precisely the one in the theorem’s stated form.

**Key facts.** `FABL.normalizedCorrelatedSignSumMeasure_upperRight_tendsto`, `FABL.coe_normalizedCorrelatedSignSumMeasure_upperRight_eq_noiseStability`, `FABL.standardGaussianUpperQuantile_upperTailOpen_biasedMajority`.

**Caveat.** The supplied informal statement discusses majority’s limiting stability and influence asymptotics, which do not match the formal theorem. The claim and proof here follow the formal theorem.

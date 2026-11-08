<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/BiasedMajorityGaussianLimit.lean :: FABL.correlatedGaussianMeasure_map_neg_biasedMajority -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simultaneous negation symmetry

**Claim.** For $-1\leq\rho\leq1$, negating both coordinates preserves the law of the correlated Gaussian pair.

**Proof.** The proof compares characteristic functions. The simultaneous negation map is multiplication by $-1$, and the characteristic function of the image measure is therefore the original characteristic function evaluated at the negated test vector. The formula for the correlated measure's characteristic function (`charFun_correlatedGaussianMeasure`) expresses this as an exponential involving its quadratic form. Since the quadratic form is unchanged by negating its argument, the resulting characteristic function is the same as before. Uniqueness of characteristic functions yields equality of the measures.

**Key facts.** `FABL.charFun_correlatedGaussianMeasure`.

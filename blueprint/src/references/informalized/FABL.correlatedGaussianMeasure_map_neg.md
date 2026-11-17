<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianThresholds.lean :: FABL.correlatedGaussianMeasure_map_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simultaneous negation symmetry

**Claim.** For $-1\leq\rho\leq1$, negating both coordinates preserves the law of the correlated Gaussian pair.

**Proof.** We compare characteristic functions. Simultaneous negation is scalar multiplication by $-1$, so the characteristic function of the image measure at a test vector is the original characteristic function evaluated at the negated vector. By `charFun_correlatedGaussianMeasure`, this is the exponential of negative one-half the correlation quadratic form at that vector. Negating the vector leaves a quadratic form unchanged, so this equals the original characteristic function. Uniqueness of characteristic functions proves equality of the measures.

**Key facts.** `FABL.charFun_correlatedGaussianMeasure`.

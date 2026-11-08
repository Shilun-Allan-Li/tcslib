<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.measure_lowDegreeF₂MissSet_le_exp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Miss probability for a nonzero polynomial

**Claim.** If the coefficient function is nonzero, the probability that a uniformly sampled $m$-tuple of Boolean-cube points consists entirely of zeros of its polynomial is at most $\exp(-m(1/2)^\ell)$.

**Proof.** First, a nonzero coefficient function defines a nonzero Boolean function: if its evaluation were identically zero, injectivity of the coefficient-to-function map would force all coefficients to vanish (`lowDegreeF₂Eval_injective`). Its algebraic degree is at most $\ell$ (`functionAlgebraicDegree_lowDegreeF₂Eval_le`). The minimum-support bound for nonzero degree-at-most-$\ell$ functions says that the fraction of inputs on which it is nonzero is at least $(1/2)^\ell$ (`inv_two_pow_le_uniformProbability_ne_zero_of_functionAlgebraicDegree_le`). Thus its zero fraction is at most $1-(1/2)^\ell$, using the complement identity for uniform probability (`uniformProbability_not`). By the product-sampling identity, the probability of missing the function on all $m$ samples is the $m$th power of this zero fraction (`measure_lowDegreeF₂MissSet_eq_pow`). Raising the bound to the $m$th power and using $1-t\le e^{-t}$ for $t=(1/2)^\ell$ gives at most $\exp(-m(1/2)^\ell)$.

**Key facts.** `FABL.lowDegreeF₂Eval_injective`, `FABL.functionAlgebraicDegree_lowDegreeF₂Eval_le`, `FABL.inv_two_pow_le_uniformProbability_ne_zero_of_functionAlgebraicDegree_le`, `FABL.uniformProbability_not`, `FABL.measure_lowDegreeF₂MissSet_eq_pow`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.measure_lowDegreeF₂SeparationFailureSet_le_of_budget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure probability under a budget

**Claim.** If $2^M\exp(-m(1/2)^\ell)\le\delta$, then the probability that the samples fail to distinguish degree-at-most-$\ell$ coefficient functions is at most $\delta$.

**Proof.** The general separation estimate bounds the failure probability by $2^M\exp(-m(1/2)^\ell)$ (`measure_lowDegreeF₂SeparationFailureSet_le`). The assumed budget bounds this expression by $\delta$, so transitivity of the order gives the result.

**Key facts.** `FABL.measure_lowDegreeF₂SeparationFailureSet_le`.

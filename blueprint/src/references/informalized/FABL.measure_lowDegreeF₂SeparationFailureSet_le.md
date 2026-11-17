<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.measure_lowDegreeF₂SeparationFailureSet_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure bound for polynomial separation

**Claim.** The probability that the samples fail to distinguish degree-at-most-$\ell$ coefficient functions is at most $2^M\exp(-m(1/2)^\ell)$, where $M$ is the number of allowed monomials.

**Proof.** If evaluation on the samples is not injective on coefficient functions, two distinct coefficient functions have identical sample evaluations. Their difference is a nonzero coefficient function whose polynomial vanishes at every sampled point. Hence the failure event is contained in the union of the miss events over all nonzero coefficient functions (`lowDegreeF₂SeparationFailureSet_subset_iUnion_missSet`). The measure of this finite union is at most the sum of the individual miss probabilities. Each is bounded by $\exp(-m(1/2)^\ell)$ (`measure_lowDegreeF₂MissSet_le_exp`), so the sum is at most the number of nonzero coefficient functions times this exponential. That number is at most the total number of coefficient functions, which is $2^M$ (`card_lowDegreeF₂Coefficients`). Combining these bounds proves the claim.

**Key facts.** `FABL.lowDegreeF₂SeparationFailureSet_subset_iUnion_missSet`, `FABL.measure_lowDegreeF₂MissSet_le_exp`, `FABL.card_lowDegreeF₂Coefficients`.

**Caveat.** The supplied informal statement describes a learning exercise, but the formal declaration proves only the stated failure-probability bound for separation.

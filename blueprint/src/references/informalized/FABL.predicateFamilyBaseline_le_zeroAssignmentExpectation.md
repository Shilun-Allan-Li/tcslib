<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.predicateFamilyBaseline_le_zeroAssignmentExpectation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Baseline and randomized expectation

**Claim.** For a nonempty finite family of sign predicates, any finite probability space and any rule selecting a predicate from each outcome, the minimum empty-set Fourier coefficient is at most the expected randomized value when every input coordinate has mean zero.

**Proof.** Regard the baseline as a constant function on the outcome space. Its expectation equals the baseline, since a probability law has total mass one (`pmfExpectation_const`). For each outcome, the selected predicate’s randomized value at zero means equals its multilinear extension there (`SignPredicate.randomizedValue_eq_multilinearExtension`); the zero means lie in the required interval. The baseline is at most this extension for each selected predicate by `predicateFamilyBaseline_le_multilinearExtension_zero`. Taking expectations preserves the pointwise inequality by monotonicity of expectation (`pmfExpectation_mono`), giving the result.

**Key facts.** `FABL.pmfExpectation_const`, `FABL.SignPredicate.randomizedValue_eq_multilinearExtension`, `FABL.predicateFamilyBaseline_le_multilinearExtension_zero`, `FABL.pmfExpectation_mono`.

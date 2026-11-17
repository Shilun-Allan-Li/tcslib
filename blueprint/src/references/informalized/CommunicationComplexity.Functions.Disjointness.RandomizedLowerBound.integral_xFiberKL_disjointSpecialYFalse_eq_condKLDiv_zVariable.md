<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.integral_xFiberKL_disjointSpecialYFalse_eq_condKLDiv_zVariable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average fiber KL as conditional KL

**Claim.** The expected fiberwise KL divergence equals the conditional KL divergence of Alice’s special bit given the statistic, relative to the uniform bit law, under the disjoint-and-special-bit-false distribution.

**Proof.** Decompose the expectation over the finite range of the statistic: each value contributes its fiber measure multiplied by the fiberwise KL divergence (`integral_xFiberKL_disjointSpecialYFalse_eq_sum_zVariable_klDiv`). The conditional KL divergence has the corresponding finite-sum formula over statistic values. Compare the summands one at a time. If a fiber has measure zero, its contribution vanishes. For every fiber of nonzero measure, the KL divergence of the law of Alice’s bit conditioned on that fiber, relative to uniform, equals the fiber’s conditional KL divergence; this is the measure-normalization identity `toReal_klDiv_map_bool_eq_KLDiv_of_measureReal_ne_zero`. Thus the two finite sums agree.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointSpecialYFalseMeasure_isProbabilityMeasure`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.integral_xFiberKL_disjointSpecialYFalse_eq_sum_zVariable_klDiv`, `ProbabilityTheory.toReal_klDiv_map_bool_eq_KLDiv_of_measureReal_ne_zero`.

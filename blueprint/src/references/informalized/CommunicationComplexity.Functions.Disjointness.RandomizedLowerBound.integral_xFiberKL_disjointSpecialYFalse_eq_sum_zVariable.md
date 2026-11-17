<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.integral_xFiberKL_disjointSpecialYFalse_eq_sum_zVariable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fiber decomposition of average KL

**Claim.** The expected fiberwise KL divergence equals the sum over statistic values of each fiber’s measure times the fiberwise KL divergence at that value.

**Proof.** The statistic has finite range, so partition the sample space into its fibers. The finite-fiber integral formula (`FiniteMeasureSpace.integral_comp_eq_sum_measureReal_fibers`) expresses the integral of a function of the statistic as the sum, over its values, of the measure of each fiber multiplied by the function’s value there. Apply this formula to the fiberwise KL divergence. The conditioned measure is a probability measure (`disjointSpecialYFalseMeasure_isProbabilityMeasure`), hence finite, as required.

**Key facts.** `CommunicationComplexity.FiniteMeasureSpace.integral_comp_eq_sum_measureReal_fibers`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointSpecialYFalseMeasure_isProbabilityMeasure`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean :: CommunicationComplexity.TVDistance.sum_singletonMassDiff_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton Mass Differences Sum to Zero

**Claim.** For probability measures μ and ν on a finite discrete measurable space Ω, the sum of their singleton mass differences is zero.

**Proof.** By distributing the sum over subtraction, the desired sum is the sum of the singleton masses of μ minus the corresponding sum for ν. The finite-space singleton formula ( `FiniteMeasureSpace.measureReal_eq_sum_singletons`) identifies each sum with the measure of Ω: every point belongs to Ω, so every indicator in that formula contributes its singleton mass. Since both measures are probability measures, each has mass one on Ω. Their difference is therefore zero.

**Key facts.** `CommunicationComplexity.FiniteMeasureSpace.measureReal_eq_sum_singletons`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.aliceInfoTermSpecialYFalse_eq_aliceCoarseInfoTermSpecialYFalse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Alice Information Terms

**Claim.** Under the law conditioned on disjointness and on Bob’s special bit being false, the conditional mutual information using Alice’s corrected conditioning equals the corresponding information using the coarse conditioning.

**Proof.** The conditioned measure is a probability measure (`disjointSpecialYFalseMeasure_isProbabilityMeasure`), so the finite-space invariance theorem for conditional mutual information applies. The first two variables, Alice’s special bit and the transcript, are unchanged. The conditioning variables agree almost everywhere by `aliceClaimConditioning_ae_eq_coarseConditioning_disjointSpecialYFalse`. Invariance under almost-everywhere equality (`ProbabilityTheory.condMutualInfo_congr_ae_finite`) gives the claimed equality.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointSpecialYFalseMeasure_isProbabilityMeasure`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.aliceClaimConditioning_ae_eq_coarseConditioning_disjointSpecialYFalse`, `ProbabilityTheory.condMutualInfo_congr_ae_finite`.

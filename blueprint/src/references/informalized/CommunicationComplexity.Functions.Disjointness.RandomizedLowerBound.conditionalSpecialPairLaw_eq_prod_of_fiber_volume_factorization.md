<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/RectangleSwitching.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialPairLaw_eq_prod_of_fiber_volume_factorization -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Law from Fiber Factorization

**Claim.** If the real masses on each special-bit pair satisfy the stated fiber-volume factorization, then the conditional law of the special-bit pair on the summary fiber is the product of the conditional laws of its two coordinates.

**Proof.** Use the criterion that the conditional pair law equals the product law when, for every pair of bits, its mass is the product of the corresponding marginal masses (conditionalSpecialPairLaw_eq_prod_of_zFiberMeasure_factorization). It remains to verify that criterion for the conditional measure on the fiber. Each such mass is the volume of the fiber intersected with the relevant event, divided by the volume of the fiber (zFiberMeasure_real_apply). The fiber has nonzero volume (volume_zFiber_ne_zero), so these denominators can be canceled. The assumed factorization of the intersected volumes then gives exactly the required factorization of the conditional masses.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialPairLaw_eq_prod_of_zFiberMeasure_factorization`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zFiberMeasure_real_apply`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_zFiber_ne_zero`.

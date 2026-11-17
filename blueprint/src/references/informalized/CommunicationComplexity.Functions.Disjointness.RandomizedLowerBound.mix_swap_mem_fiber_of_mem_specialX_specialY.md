<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/RectangleSwitching.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.mix_swap_mem_fiber_of_mem_specialX_specialY -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Swapping Mixed Samples Preserves a Fiber

**Claim.** If two samples lie in the same fiber, then mixing Alice’s input from the second with Bob’s input from the first also lies in that fiber.

**Proof.** The fiber hypotheses give $Z(\omega_X)=z$ and $Z(\omega_Y)=z$. Apply the mixing property for equal $Z$ values (`zVariable_mix_eq_of_same_zVariable`) with the samples in the order $\omega_Y,\omega_X$. It gives $Z(\operatorname{mix}(\omega_Y,\omega_X))=z$, which is exactly membership in the fiber.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zVariable_mix_eq_of_same_zVariable`.

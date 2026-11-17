<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.integral_xFiberKL_disjointSpecialYFalse_eq_aliceInfoTermSpecialYFalse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fiber KL equals Alice’s information term

**Claim.** The expected fiberwise KL divergence under the disjoint-and-special-bit-false distribution equals Alice’s special-bit conditional information term under that distribution.

**Proof.** The information term conditioned on Bob’s special bit being false equals the corresponding coarse conditional information term (`aliceInfoTermSpecialYFalse_eq_aliceCoarseInfoTermSpecialYFalse`). The expected fiber KL divergence equals that coarse term (`integral_xFiberKL_disjointSpecialYFalse_eq_aliceCoarseInfoTermSpecialYFalse`). Substituting the first equality into the second gives the claim.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.aliceInfoTermSpecialYFalse_eq_aliceCoarseInfoTermSpecialYFalse`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.integral_xFiberKL_disjointSpecialYFalse_eq_aliceCoarseInfoTermSpecialYFalse`.

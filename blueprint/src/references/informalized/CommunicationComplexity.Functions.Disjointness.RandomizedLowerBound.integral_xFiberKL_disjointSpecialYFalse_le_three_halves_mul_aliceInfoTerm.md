<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/Headline.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.integral_xFiberKL_disjointSpecialYFalse_le_three_halves_mul_aliceInfoTerm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average fiber KL bound

**Claim.** The expected fiberwise KL divergence is at most three halves times Alice’s conditional information term under the disjoint-input distribution.

**Proof.** The expected fiberwise KL divergence equals Alice’s information term conditioned on Bob’s special bit being false (`integral_xFiberKL_disjointSpecialYFalse_eq_aliceInfoTermSpecialYFalse`). The information comparison gives $(2/3)$ times this conditioned term at most the full Alice information term (`two_thirds_mul_aliceInfoTermSpecialYFalse_le_aliceInfoTerm`). Since $2/3$ is positive, rearranging yields the desired upper bound by $3/2$ times the full term.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.integral_xFiberKL_disjointSpecialYFalse_eq_aliceInfoTermSpecialYFalse`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.two_thirds_mul_aliceInfoTermSpecialYFalse_le_aliceInfoTerm`.

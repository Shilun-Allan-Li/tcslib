<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/InformationTerms.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.aliceInfoTerm_eq_sum_specialCoordinate_fiber_info -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Special-coordinate fiber decomposition

**Claim.** For positive $n$, Alice’s information term under the disjoint-conditioned hard-sample distribution is the average, over the special coordinate, of the corresponding conditional information on that coordinate’s fiber.

**Proof.** The conditioning tuple used in Alice’s information term is exactly the pair consisting of the special coordinate and Alice’s dynamic conditioning data, by the identity expressing `aliceClaimConditioning` as that product (`aliceClaimConditioning_eq_specialCoordinate_prod_dynamic`). The conditional mutual information decomposition over a finite-valued conditioning component then writes the information conditioned on this pair as a sum over coordinates $i$, weighted by the disjoint-conditioned measure of the fiber where the special coordinate equals $i$ (`ProbabilityTheory.condMutualInfo_prod_conditioning_eq_sum`). Each such fiber has measure $1/n$ (`disjointCondMeasure_measureReal_specialCoordinate_preimage_singleton`), giving the stated average.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.aliceClaimConditioning_eq_specialCoordinate_prod_dynamic`, `ProbabilityTheory.condMutualInfo_prod_conditioning_eq_sum`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measureReal_specialCoordinate_preimage_singleton`.

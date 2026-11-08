<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.tvDistance_eq_densityPositiveIntegral_of_ac -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total variation and density excess

**Claim.** For probability measures μ and ν with μ absolutely continuous with respect to ν, their total variation distance equals the integral of the density excess over the region where the density is at least one.

**Proof.** Use the equality between total variation distance and the supremum over measurable sets of the absolute measure difference (CommunicationComplexity.TVDistance.tvDistance_eq_tvDistanceSup). The supremum formula identifies that quantity, under absolute continuity, with the integral of the density excess over the region where the density is at least one (CommunicationComplexity.tvDistanceSup_eq_densityPositiveIntegral_of_ac). Combining these equalities gives the claim.

**Key facts.** `CommunicationComplexity.TVDistance.tvDistance_eq_tvDistanceSup`, `CommunicationComplexity.tvDistanceSup_eq_densityPositiveIntegral_of_ac`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/InformationTerms.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.fixedAliceCrossInfoTerm_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing cross-information term

**Claim.** For each coordinate $i$, the conditional mutual information between Alice's bit and Bob's prefix, given Alice's conditioning data under the disjoint-conditioned hard measure, is zero.

**Proof.** Write $\nu$ for the uniform distribution on disjoint coordinate vectors. The joint triple consisting of Alice's bit, Bob's prefix, and the conditioning data under the conditioned hard measure has the same distribution as the corresponding triple extracted from a vector distributed according to $\nu$ (`identDistrib_fixedAliceCrossInfoTriple_uniform`). Conditional mutual information depends only on this joint distribution, so the two conditional mutual informations agree (`ProbabilityTheory.IdentDistrib.condMutualInfo_eq_finite`). For the uniform disjoint-coordinate-vector model, the cross-information term is zero (`uniformDisjointCoordinateVector_crossInfo_eq_zero`); therefore the original term is zero too.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.identDistrib_fixedAliceCrossInfoTriple_uniform`, `ProbabilityTheory.IdentDistrib.condMutualInfo_eq_finite`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_crossInfo_eq_zero`.

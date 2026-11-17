<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/InformationTerms.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.aliceInfoTerm_dualProtocol_eq_bobInfoTerm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality of Information Terms

**Claim.** The information term for Alice under the dual protocol equals Bob’s information term for the original protocol.

**Proof.** Unfold the two information terms. The shared duality identity for conditional mutual information of protocol transcripts (`condMutualInfo_message_dualProtocol_eq`) applies once its variable identities are supplied. Alice’s special bit on the dual sample is Bob’s special bit on the original sample (`specialX_dualHardSample`). Alice’s conditioning triple on the dual sample is the dual recoding of Bob’s conditioning triple on the original sample (`aliceClaimConditioning_dualHardSample`). These identities fulfill the hypotheses of the shared result, yielding the equality.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.condMutualInfo_message_dualProtocol_eq`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialX_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.aliceClaimConditioning_dualHardSample`.

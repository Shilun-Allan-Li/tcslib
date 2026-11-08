<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/InformationTerms.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.bobInfoTerm_dualProtocol_eq_aliceInfoTerm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality of information terms

**Claim.** Bob’s information term for the dual protocol equals Alice’s information term for the original protocol.

**Proof.** Expand the definitions of Bob’s and Alice’s information terms. The shared duality theorem for conditional mutual information of protocol transcripts says that the information for a dual bit and dual conditioning variable under the dual protocol equals the original conditional mutual information, provided the bit and conditioning variable transform correctly under the dual-sample map (`condMutualInfo_message_dualProtocol_eq`). Here Bob’s special bit on the dual sample equals Alice’s special bit on the original sample (`specialY_dualHardSample`), and Bob’s conditioning variable on the dual sample is the dual recoding of Alice’s conditioning variable (`bobClaimConditioning_dualHardSample`). Applying the theorem with these identities yields the equality.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.condMutualInfo_message_dualProtocol_eq`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialY_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.bobClaimConditioning_dualHardSample`.

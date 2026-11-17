<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/InformationTerms.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.claimInfo_dualProtocol -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality Invariance of Claim Information

**Claim.** The sum of Alice’s and Bob’s claim information for a protocol is unchanged when the protocol swaps the parties and reverses the coordinate order.

**Proof.** By the duality identities, Alice’s information term for the dual protocol equals Bob’s information term for the original protocol (aliceInfoTerm_dualProtocol_eq_bobInfoTerm), and Bob’s information term for the dual equals Alice’s for the original (bobInfoTerm_dualProtocol_eq_aliceInfoTerm). Substituting these into the definition of claim information reverses the two summands. Their sum is unchanged because addition is commutative.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.aliceInfoTerm_dualProtocol_eq_bobInfoTerm`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.bobInfoTerm_dualProtocol_eq_aliceInfoTerm`.

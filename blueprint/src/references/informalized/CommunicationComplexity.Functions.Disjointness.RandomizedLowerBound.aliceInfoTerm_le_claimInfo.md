<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/InformationTerms.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.aliceInfoTerm_le_claimInfo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Alice information is bounded by claim information

**Claim.** Alice’s information term is at most the sum of Alice’s and Bob’s information terms, which is the total claim information.

**Proof.** By definition, total claim information is Alice’s information term plus Bob’s. Bob’s information term is nonnegative (`bobInfoTerm_nonneg`), so adding it to Alice’s term cannot decrease the value. This is the asserted inequality.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.bobInfoTerm_nonneg`.

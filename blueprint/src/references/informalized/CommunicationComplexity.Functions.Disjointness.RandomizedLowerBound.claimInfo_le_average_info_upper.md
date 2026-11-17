<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/InformationTerms.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.claimInfo_le_average_info_upper -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Claim Information Upper Bound

**Claim.** The claim information of a deterministic protocol is at most $\frac{2C(p)\log 2}{n}$, where $C(p)$ is its worst-case number of bits exchanged.

**Proof.** Alice’s claim information is at most $\frac{C(p)\log 2}{n}$ by the average entropy bound for Alice (aliceInfoTerm_le_average_entropy_bound). The corresponding bound for Bob (bobInfoTerm_le_average_entropy_bound) gives the same upper bound for his term. Adding the two inequalities bounds their sum by two copies of $\frac{C(p)\log 2}{n}$; rearranging this expression gives the claimed bound.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.aliceInfoTerm_le_average_entropy_bound`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.bobInfoTerm_le_average_entropy_bound`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/RectangleSwitching.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.mem_goodZEvent_of_xDistance_yDistance_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closeness of the Special Bit Pair

**Claim.** If each conditional special bit is within total variation distance $\gamma$ of a uniform bit, then the conditional law of their pair is within distance $2\gamma$ of a uniform bit pair.

**Proof.** Apply the bound that the pair’s total variation distance is at most the sum of the two marginal distances (`zDistance_le_xDistance_add_yDistance`). The hypotheses bound each summand by $\gamma$, so their sum is at most $2\gamma$. By the definition of the good event, this is exactly the required membership.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zDistance_le_xDistance_add_yDistance`.

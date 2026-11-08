<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.input_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input transformation under duality

**Claim.** The dual sample produces the input pair obtained by swapping the two input sets and reversing their coordinate order.

**Proof.** For the dual sample, the Alice input set is the reversal of the original Bob input set, by the duality identity for $X$ (`X_dualHardSample`). Its Bob input set is the reversal of the original Alice input set, by the corresponding identity for $Y$ (`Y_dualHardSample`). Since an input pair is the ordered pair of these two sets, the stated formula follows.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.X_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.Y_dualHardSample`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.dualConditioningValue_dualConditioningValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Involutivity of dual conditioning

**Claim.** The dual conditioning-value recoding, which reverses the coordinate, reverses both Boolean vectors, and swaps their order, returns every triple to itself when applied twice.

**Proof.** Write the triple as $(i,x,y)$. Applying the recoding twice reverses the coordinate twice, so the coordinate returns to $i$. The two vector reversals also each undo themselves, by the fact that reversing a Boolean vector twice gives the original vector (`reverseBoolVector_reverseBoolVector`). The swap of the two vectors occurs twice as well. Thus every component agrees with the original triple.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.reverseBoolVector_reverseBoolVector`.

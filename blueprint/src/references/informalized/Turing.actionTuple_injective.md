<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPPHard.lean :: Turing.actionTuple_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Action Record

**Claim.** For any natural number $k$ and type $S$, the map sending an action with $k$ work tapes, binary symbols, and states in $S$ to its input-head move, work-tape data, output symbol, and successor state is injective.

**Proof.** Take two actions whose associated tuples are equal. Equality of ordered tuples forces equality of each corresponding component: their input-head moves agree, their work-tape data agree as functions on the tape indices, their output symbols agree, and their successor states agree. An action is determined by these four fields, so the two actions are equal. This proves injectivity.

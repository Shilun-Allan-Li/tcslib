<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.xorPairEmit_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty Output for an Empty Component

**Claim.** If either component string is empty, the pair-output rule on their encoding returns the empty string.

**Proof.** If the first component is empty, the rule detects an empty first projection and returns the empty string. If instead the second component is empty, it detects an empty second projection and likewise returns the empty string. These cases cover the stated disjunction.

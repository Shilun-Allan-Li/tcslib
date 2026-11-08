<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.Bd.of_toV -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate bounds imply state bounds

**Claim.** If every entry of the coordinate vector of a state record is at most $B$, then each of its fifteen coordinates is at most $B$.

**Proof.** The coordinate vector lists the state coordinates in order. Evaluate the assumed bound at each of the fifteen coordinate indices; the resulting inequalities are exactly the fifteen conjuncts asserting that the state coordinates are bounded by $B$.

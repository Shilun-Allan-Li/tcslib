<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_copy_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register-Copy Run

**Claim.** If the registers are bounded by $B$ and the source value is at least the destination value, the copy loop reaches its prescribed next state with the destination replaced by the source value, maintaining the configuration invariant throughout.

**Proof.** At stage $s$, the machine compares the destination and source registers. If they are equal, it exits to the state prescribed for that stage. Otherwise, it increments the destination and returns to the comparison. Since the source is fixed and the destination begins no larger than it, this loop terminates exactly when the two values agree, leaving the destination equal to the original source value. The copy-loop theorem (`Complexity.LogProg.registerCopy_loop`) establishes this run and its register bounds. The stage table confirms that the destination and source are distinct and that each stage's instructions have the required comparison-and-increment form; the remaining invariant is the prescribed one in that theorem.

**Key facts.** `Complexity.LogProg.registerCopy_loop`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.drop_copy_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Copy-Register Run

**Claim.** In any copy stage, if all nine registers initially hold at most $4|h|+4$ and the source register is no larger than the destination register, the register machine reaches the next stage with the source register replaced by the destination's initial value. Before the final configuration, every configuration satisfies the machine's validity conditions and keeps all registers at most $4|h|+4$.

**Proof.** At the specified stage, the machine repeatedly compares the destination and source registers. If they differ, it increments the destination and returns to the comparison; when they agree, it moves to the next stage. Since the source initially is at least as large as the destination, this process terminates when the destination has reached the source's initial value. The copy-loop theorem (Complexity.LogProg.registerCopy_loop) packages this run: it requires the two registers to be distinct, the stated initial bound, and the initial ordering, and guarantees the endpoint with the destination updated to the source value. Here the stage data supplies the comparison and increment instructions, the source and destination are distinct, and the bound is $4|h|+4$. The theorem also preserves the stated safety predicate and register bound throughout the run.

**Key facts.** `Complexity.LogProg.registerCopy_loop`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying a register value

**Claim.** For a chosen copy stage, if the destination register initially does not exceed the source register, the copy routine reaches its specified next state with the destination replaced by the source's original value and all other registers unchanged.

**Proof.** The copy routine repeatedly compares the destination and source. If they are equal, it exits to the stage's designated next state. Otherwise, the comparison sends it to a bump state, which increments the destination and returns to the comparison. Since the destination initially does not exceed the source, this loop terminates when the two registers agree; the source is never modified, and the destination then equals its original source value. All other registers remain fixed. The general register-copy loop theorem supplies this reachability for distinct destination and source registers when the initial register values satisfy the stated order (`registerCopy_loop`).

**Key facts.** `Complexity.LogProg.registerCopy_loop`.

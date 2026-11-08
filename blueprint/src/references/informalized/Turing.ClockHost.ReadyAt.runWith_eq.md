<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean :: Turing.ClockHost.ReadyAt.runWith_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State and Output Agreement for Short Runs

**Claim.** If $a$ is ready at $m$ and $|u|\le m$, then running $A$ on $u$ from $a$ and from its initial configuration on $x$ yields the same state and output.

**Proof.** Compare $a$ with the initial configuration using the relation `AgreeShift` at shift $|u|$. Readiness gives agreement of their state, input-head position, and output, while their work-tape heads initially agree because readiness places them at the required initial positions. The initial configuration has blank work tapes; readiness says the tape contents of $a$ are blank throughout the region needed for this comparison. Since $|u|\le m$, the readiness blank-region hypothesis supplies that agreement. The preservation theorem for `AgreeShift` says that after running the same choice word, the two configurations still satisfy the relation (`AgreeShift.runWith`). Its state and output clauses give exactly the two desired equalities.

**Key facts.** `Turing.NDTM.AgreeShift.runWith`.

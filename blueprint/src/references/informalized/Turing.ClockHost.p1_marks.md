<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean :: Turing.ClockHost.p1_marks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run Through the Second Reset Sweep

**Claim.** Starting in phase $p1$ with the yard head at $m-|w|$, running the host on a choice word $w$ of length at most $m$ leaves it in phase $p1$, advances each of $A$'s work-head positions by $|w|$, and places the yard head at $m$, leaving the other listed data and output unchanged.

**Proof.** Induct on $w$, allowing the simulated work-head positions to vary. The empty word leaves the configuration unchanged. For a nonempty word with first bit $b$ and suffix $w$, the length bound ensures that the yard position $m-(|w|+1)$ is nonnegative and strictly below $m$, so it is marked (`yard_of_lt`). The run-on-cons law (`runWith_cons`) and the marked-step result (`p1_mark`) show that the first step advances the yard head to $m-|w|$ and each simulated work head by one. The induction hypothesis now applies to the suffix. Its additional $|w|$ advances put the yard head at $m$ and give a total work-head advance of $|w|+1$, proving the assertion.

**Key facts.** `Turing.NDTM.runWith_cons`, `Turing.ClockHost.yard_of_lt`, `Turing.ClockHost.p1_mark`.

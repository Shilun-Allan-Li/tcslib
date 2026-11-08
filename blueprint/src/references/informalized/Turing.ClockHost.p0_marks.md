<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean :: Turing.ClockHost.p0_marks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run Through the First Reset Sweep

**Claim.** Starting in phase $p0$ with the yard head at $|w|-1$, running the host on a choice word $w$ of length at most $m$ leaves it in phase $p0$, with the input head moved left with clamping $|w|$ times, each of $A$'s work-head positions advanced by $|w|$, and the yard head at $-1$; the other listed data and output are unchanged.

**Proof.** Induct on the choice word, allowing the initial input position and work-head positions to vary. For the empty word, the run changes nothing, and the claimed positions and phase reduce to their starting values. For a word with first bit $b$ and remaining suffix $w$, the length bound ensures that the yard head at $|w|$ is a marked cell (`yard_of_lt`). The run-on-cons law (`runWith_cons`) reduces the first step to the marked-cell transition (`p0_mark`): the input head moves left once, each of $A$'s work heads advances once, and the yard head moves to $|w|-1$. The induction hypothesis applies to the suffix from this new configuration. Combining its left moves and work-head advances with the first step gives the claimed totals; the yard head ends at $-1$.

**Key facts.** `Turing.NDTM.runWith_cons`, `Turing.ClockHost.yard_of_lt`, `Turing.ClockHost.p0_mark`.

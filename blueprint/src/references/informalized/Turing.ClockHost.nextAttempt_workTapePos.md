<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean :: Turing.ClockHost.nextAttempt_workTapePos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Head Bounds After a Next Attempt

**Claim.** After the next-attempt reset applied to the run of $A$ from $a$ under a choice word $u$ of length $m$, each work-head position lies between its initial position plus $2m+3$ and plus $4m+3$.

**Proof.** Fix a work tape. The run under $u$ changes its head position by an amount whose absolute value is at most $|u|$ (`abs_runWith_workTapePos_sub_le`), hence at most $m$. The next-attempt reset adds $3(m+1)=3m+3$ to that run's position. Adding the displacement bound to this reset offset gives a total change between $3m+3-m=2m+3$ and $3m+3+m=4m+3$, as required.

**Key facts.** `Turing.NDTM.abs_runWith_workTapePos_sub_le`.

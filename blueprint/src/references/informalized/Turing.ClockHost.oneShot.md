<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean :: Turing.ClockHost.oneShot -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Preservation in One Clocked Attempt

**Claim.** With looping disabled, the host run on a choice word of length $m+1$ halts, and its output is exactly $[v]$ if and only if the run of $A$ on the first $m$ bits halts with output exactly $[v]$.

**Proof.** Split the choice word into a prefix $u$ of length $m$, a final bit $b$, and a suffix of length zero (`exists_split_block`). Thus the word is $u++[b]$, and its first $m$ bits are exactly $u$. Running the host on $u$ corresponds to running $A$ on $u$, with the host's yard head at the timeout position (`run_run_zero`); the run concatenation and cons laws (`runWith_append`, `runWith_cons`, `runWith_nil`) identify the remaining step with the host's timeout check on the resulting configuration $a'$. If $a'$ has halted with a singleton output $[v]$, the timeout-success rule (`timeout_success`) makes the host halt with precisely that output. Otherwise the timeout-failure rule (`timeout_fail`) makes it halt with empty output. In this second case the host cannot output any singleton, and $A$ cannot have both halted and produced a singleton; this proves the claimed equivalence for every $v$ as well as host termination.

**Key facts.** `Turing.ClockHost.exists_split_block`, `Turing.NDTM.runWith_append`, `Turing.ClockHost.run_run_zero`, `Turing.NDTM.runWith_cons`, `Turing.NDTM.runWith_nil`, `Turing.ClockHost.timeout_success`, `Turing.ClockHost.timeout_fail`.

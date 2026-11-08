<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean :: Turing.ClockHost.round -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Clocked Round

**Claim.** Starting from a clock-ready host configuration, a choice word of length $4(m+1)$ simulates the first $m$ choices of $A$ and then resets the clock. If that run halts with output the single bit $v$, the host halts with output $v$; if it does not halt with a single-bit output, the host returns to a clock-ready configuration.

**Proof.** Unpack clock-readiness: the host configuration represents a configuration $a$ of $A$ satisfying the ready conditions, together with the yard at zero. Split the word as $u$ followed by a bit $b$ and a suffix $r$, where $|u|=m$ and $|r|=3(m+1)$ (`exists_split_block`). The first $m$ choices simulate $A$ on $u$; the clock-run simulation theorem `run_run_zero` places the host at the corresponding simulated configuration with yard head at $m$. The ready-state comparison `ReadyAt.runWith_eq` ensures that the state and output of this simulated configuration agree with those of $A$ run from its initial configuration on the first $m$ choices; these are exactly the choices in the prefix of the original word.

Now consider the next choice $b$. If the simulated configuration has halted with output $[v]$, the timeout-success rule says the host halts with output $[v]$ (`timeout_success`). Since an already halted machine remains unchanged under further choices (`runWith_of_halt`), the remaining suffix leaves this result intact. Otherwise, `timeout_fail` sends the host into the first reset phase. The suffix $r$ has the exact length required by `reset_run`, which carries out the reset and starts the next attempt. Finally, `ReadyAt.next` shows that the resulting attempt configuration is ready, using $|x|\le m$ and $|u|=m$; the reset result is therefore clock-ready as required.

**Key facts.** `Turing.ClockHost.exists_split_block`, `Turing.ClockHost.ReadyAt.runWith_eq`, `Turing.ClockHost.run_run_zero`, `Turing.ClockHost.timeout_success`, `Turing.NDTM.runWith_of_halt`, `Turing.ClockHost.timeout_fail`, `Turing.ClockHost.reset_run`, `Turing.ClockHost.ReadyAt.next`.

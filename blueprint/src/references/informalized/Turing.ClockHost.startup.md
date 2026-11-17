<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean :: Turing.ClockHost.startup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Startup reaches the initial run configuration

**Claim.** If the deterministic machine halts on $x$ with output consisting of $m$ true symbols by time $T$, and $|x|\le m$, then there is a length $s_0\le T+m+2$ such that every choice word of length $s_0$ brings the host to the initial configuration of the nondeterministic machine, with clock value zero and suitable fixed work tapes and head positions for the deterministic machine.

**Proof.** 1. The assumed computation supplies a halting time $T$. Choose the least halting time $t_* = \operatorname{Nat.find}(\text{halting-time witness})$. Then $t_*\le T$, and the deterministic machine is still running at every time strictly before $t_*$. Let $c_S$ be its configuration at time $t_*$. It is halted, and its output is exactly the prescribed word of $m$ true symbols: the output agrees with that of the given halting computation by uniqueness of outputs across halting computations.

2. Set $s_0=t_*+(m+2)$, and choose the deterministic work-tape contents and head positions from $c_S$. Split any choice word $w$ of length $s_0$ after its first $t_*$ bits. The boot simulation on that prefix follows the deterministic computation through time $t_*$: every earlier configuration is live, so the boot simulation applies. Thus it reaches the boot configuration encoding $c_S$. The remaining suffix has length $m+2$.

3. Since $c_S$ is halted and its output has the required form, the boot configuration is the rewind-phase configuration with deterministic work tapes fixed, the length-$m$ yardstick on the clock tape, and its head at $m$. The rewind simulation consumes any suffix of length $m+2$ and reaches the run phase with the nondeterministic machine in its initial state, the same input position and both sets of work tapes and head positions, and clock head at zero. The input head is restored to its initial position because the length bound $|x|\le m$ makes the rewind sweep reach the left boundary. This resulting configuration is exactly the claimed one. Finally, $t_*\le T$ gives $s_0\le T+m+2$.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.output_unique`, `Turing.ClockHost.boot_run`, `Turing.ClockHost.initCfg_eq_bootCfg`, `Turing.NDTM.runWith_append`, `Turing.ClockHost.rewind_run`, `Turing.ClockHost.moveInputPos_inLeft`.

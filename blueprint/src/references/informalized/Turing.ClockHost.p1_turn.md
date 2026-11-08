<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean :: Turing.ClockHost.p1_turn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Sweep Turnaround

**Claim.** A host step from phase $p1$, with the yard head at $m$ on a yard of length $m$, preserves the simulated tapes and output, advances each work-tape head of $A$ by one, leaves the input head fixed, and enters phase $p2$ with yard head at $m-1$.

**Proof.** The host-step equation identifies this transition with the action prescribed by the phase rule (`stepWith_hostCfg`). At the yard head position $m$, the yard tape is blank (`yard_len`), so the $p1$ rule takes its blank-cell branch: it moves the input head by zero, advances each of $A$'s work heads by one, makes no tape writes or output, moves the yard head left by one, and changes the phase to $p2$. Applying this action to the host configuration gives the stated equality; the action's effect on the separated tape slots is recorded by `apply_hostCfg`.

**Key facts.** `Turing.ClockHost.stepWith_hostCfg`, `Turing.ClockHost.yard_len`, `Turing.ClockHost.apply_hostCfg`.

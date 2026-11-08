<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean :: Turing.ClockHost.p2_turn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reset Sweep Turnaround

**Claim.** From phase $p2$ with the yard head at $-1$, one host step preserves $S$'s tapes and heads and all tape contents, advances each work-tape head of $A$ by one, moves the input head right by one with boundary clamping, and enters the running phase with $A$ in its initial state and no captured output; the yard head becomes zero.

**Proof.** The host-step equation reduces the claim to evaluating the phase transition (`stepWith_hostCfg`). The yard tape is blank at position $-1$ (`yard_neg_one`), so phase $p2$ takes its blank-cell branch. That branch moves the input head one place right, leaves the $S$ tapes idle, advances every $A$ work head by one without writing, and moves the yard head right by one. It sets the state to the running phase with $A$'s initial state and an empty capture, and produces no output. Applying this action to the configuration gives the claimed result (`apply_hostCfg`).

**Key facts.** `Turing.ClockHost.stepWith_hostCfg`, `Turing.ClockHost.yard_neg_one`, `Turing.ClockHost.apply_hostCfg`.

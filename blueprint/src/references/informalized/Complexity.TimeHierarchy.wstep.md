<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockLoop.lean :: Complexity.TimeHierarchy.wstep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Clock Simulation

**Claim.** When the clock machine is in its decoding phase and the clock cell at its head contains $1$, one step simulates one step of the machine being decoded, updates the clock cell and head, and emits the specified halting indicator when the simulated transition halts.

**Proof.** First, since the simulated configuration has state $q$, the step of $W$ is exactly the result of applying its transition action at $q$ to that configuration. Next, the clock machine is in a nonhalting clock state, so its step is given by the action prescribed by its transition function (`clockTM_step_some`). In the decoding state, the clock head reads the central buffer cell; the hypothesis that this cell contains $1$ selects the branch that writes $0$, moves the clock head one position left, and applies $W$'s transition action to the right-hand block of tapes. The central-cell identity (`ctrCfg_ctr`) verifies the symbol read, while `ctrCfg_right` identifies the symbols on the simulated machine's tapes with those of $c$. The tape-block definitions then show that the left block is unchanged and the right block evolves exactly as in $W$'s step. The resulting state is the return state carrying the updated output register when the transition continues, and is halting otherwise; in the latter case the emitted bit is precisely the stated test of whether the updated register is the one-register.

**Key facts.** `Complexity.TimeHierarchy.clockTM_step_some`, `Complexity.TimeHierarchy.ctrCfg_ctr`, `Complexity.TimeHierarchy.ctrCfg_right`.

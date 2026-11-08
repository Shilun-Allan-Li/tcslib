<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockLoop.lean :: Complexity.TimeHierarchy.underflow_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clock Underflow Halts

**Claim.** If the clock tape is blank at the current clock-head position, one step from the decrement state halts and appends the single bit $1$ to the empty output.

**Proof.** The clock transition rule (`clockTM_step_some`) expresses the step as the action prescribed in state $\mathrm{dec}$. The clock-cell lemma (`ctrCfg_ctr`) identifies the scanned clock symbol as $\tau(z)$, which is blank by assumption. In the blank-cell branch, the transition halts and emits $\mathrm{true}$. Applying that action to the configuration leaves the output as the singleton list $[\mathrm{true}]$, proving both claims.

**Key facts.** `Complexity.TimeHierarchy.clockTM_step_some`, `Complexity.TimeHierarchy.ctrCfg_ctr`.

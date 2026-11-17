<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlockLoop.lean :: Turing.StepBlock.loopOrbit_rep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Representation Along Loop Iterations

**Claim.** If the simulated machine remains in a present state before each of the first $r$ steps, then after $r$ compiled rounds the compiled configuration is at the exit anchor determined by whether the simulated machine is still running, represents its configuration at time $r$, and has the original output.

**Proof.** Induct on $r$. At $r=0$, the round orbit is the starting configuration. The zero-step run identity identifies the simulated configuration with $c$, and the assumed live starting state makes the exit selected by the current simulated state the live anchor. The given anchor and representation hypotheses then establish all three conclusions. For the successor step, the induction hypothesis gives the compiled configuration after $r$ rounds at the live anchor, representing the simulated configuration at time $r$ and preserving its output. The live-state assumption at time $r$ supplies the hypothesis needed to apply `loopRoundTime_spec` to this configuration. That result says the next compiled round reaches the anchor selected by the state after one simulated step, preserves the representation and output, and reaches an exit. The orbit successor identity (`loopOrbit_succ`) identifies the $(r+1)$-round orbit with precisely this next run, while the run successor identity (`runFrom_succ_eq_step'`) identifies the simulated configuration after $r+1$ steps with that one-step successor. Combining these identities with the induction conclusions proves the claim.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.StepBlock.loopRoundTime_spec`, `Turing.StepBlock.loopOrbit_succ`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.

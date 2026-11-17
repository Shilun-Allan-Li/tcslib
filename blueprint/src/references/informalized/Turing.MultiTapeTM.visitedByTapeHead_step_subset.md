<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.MultiTapeTM.visitedByTapeHead_step_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Visited Cells After One Initial Step

**Claim.** The initial head position, together with the cells visited for $t$ steps from the one-step successor, is contained in the cells visited through step $t+1$ from the original configuration.

**Proof.** A cell in the union is either the original head position or a position visited at some time $v\leq t$ from the one-step successor. The original head position is visited at time zero, by `runFrom_zero`. In the other case, the run decomposition after one initial step (`runFrom_succ_eq_step`) identifies that position with the position at time $v+1$ from the original configuration. Since $v+1\leq t+1$, it belongs to the visited set through step $t+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.

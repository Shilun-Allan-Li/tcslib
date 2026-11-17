<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigStep.lean :: Complexity.abs_workTapePos_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Tape Head Displacement Bound

**Claim.** After a finite Turing machine runs on a binary word for $t$ steps, the absolute value of the head position on any work tape is at most $t$.

**Proof.** Induct on $t$. At time zero, the work-tape head starts at position $0$, so the bound holds. For the induction step, the run at time $t+1$ is one step from the configuration at time $t$ (`Turing.MultiTapeTM.runFrom_succ_eq_step'`). In one step, the head position changes by at most one (`Turing.MultiTapeTM.workTapePos_step_le`). Combining this with the induction hypothesis $|p_t|\le t$ gives $|p_{t+1}|\le t+1$ by the triangle inequality. This proves the bound for every $t$.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.workTapePos_step_le`.

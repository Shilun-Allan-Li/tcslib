<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_head_steps -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Head Displacement Bound

**Claim.** After $t$ steps, each work-tape head lies between its initial position minus $t$ and its initial position plus $t$.

**Proof.** Induct on $t$. At time zero the head is at its initial position, so both inequalities hold. For the successor step, each single transition changes a work-head position by at most one, as expressed by the work-head step bound (`Turing.MultiTapeTM.workTapePos_step_le`). Apply that bound to the configuration at time $t$, and use the induction bounds to place the new position between the initial position minus $(t+1)$ and the initial position plus $(t+1)$.

**Key facts.** `Turing.MultiTapeTM.workTapePos_step_le`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.

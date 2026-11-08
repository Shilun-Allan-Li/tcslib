<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Finite.lean :: Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Tape Head Displacement Bound

**Claim.** For every number of steps $u$ and every work-tape index $j$, the head position after running from $c$ for $u$ steps lies between its initial position minus $u$ and its initial position plus $u$.

**Proof.** Proceed by induction on $u$. At zero steps the head remains at its initial position, so both interval bounds hold. For the successor step, the induction hypothesis places the position after $u$ steps within distance $u$ of its initial position. One further machine step changes this head position by at most $1$ in absolute value (the one-step movement bound, `workTapePos_step_le`). Hence the new position is at least the initial position minus $u+1$ and at most the initial position plus $u+1$. The identity expressing a run of $u+1$ steps as one step after the run of $u$ steps (`runFrom_succ_eq_step'`) identifies this position with the one in the claim.

**Key facts.** `Turing.MultiTapeTM.workTapePos_step_le`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loop_input_run_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-head Position Bound After a Run

**Claim.** After $t$ steps from configuration $c$, the input-head position is at most its initial position plus $t$.

**Proof.** First establish the one-step estimate for an arbitrary configuration. If it is already halted, one step leaves it unchanged. Otherwise the transition applies an action, whose input-head position is obtained by the clamped movement; the one-step movement bound (`Turing.FinTM.f2_loop_input_move_le`) therefore increases the position by at most one. Now induct on $t$. The zero-step run leaves the position unchanged. For the successor case, the run through $t+1$ steps is one step applied to the configuration reached after $t$ steps (`Turing.MultiTapeTM.runFrom_succ_eq_step'`). Apply the one-step estimate there and combine it with the induction bound to obtain the initial position plus $t+1$.

**Key facts.** `Turing.FinTM.f2_loop_input_move_le`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.

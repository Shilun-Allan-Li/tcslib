<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockLoop.lean :: Complexity.TimeHierarchy.borrow_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Borrowing Steps in the Clock Computation

**Claim.** Starting the clock machine in the decrement state with $i$ true counter symbols followed by $j$ false symbols, counter head at $i$, unchanged simulated configuration and other work tapes, and empty output, after $j$ steps it is still in that decrement state with $i+j$ true symbols followed by the rest and counter head at $i+j$.

**Proof.** Induct on the number $j$ of false symbols. When $j=0$, the initial counter tape and head already have the claimed form. For the inductive step, suppose the counter contains $i$ true symbols, then $j+1$ false symbols, then the rest, with its head at $i$. By the indexing fact `bufferTape_nat`, the symbol under the head is the first false symbol. In the decrement state, the clock transition writes true there, moves the counter head one place right, and keeps the state and the simulated machine's configuration, the other tapes, and output unchanged. The buffer update identity `bufferTape_update_mid` identifies the resulting tape with one containing $i+1$ true symbols followed by $j$ false symbols and the rest. The transition calculation is expressed by `clockTM_step_some`, `ctrCfg_ctr`, and `ctrAction_apply`. Apply the induction hypothesis to these $j$ remaining false symbols, now starting with $i+1$ true symbols. This yields $i+1+j$ true symbols and head position $i+1+j$, which equal the claimed $i+(j+1)$; the iteration identity `runFrom_succ_eq_step` relates this first transition followed by $j$ further steps to the full run.

**Key facts.** `Turing.FinTM.bufferTape_nat`, `Complexity.TimeHierarchy.ctrCfg_ctr`, `Complexity.TimeHierarchy.clockTM_step_some`, `Complexity.TimeHierarchy.ctrAction_apply`, `Complexity.TimeHierarchy.bufferTape_update_mid`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.

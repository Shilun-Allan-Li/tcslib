<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineSetup.lean :: Complexity.Meyer.rewX_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the First Auxiliary Tape

**Claim.** For every $j\le |w|$, after $j+1$ steps from the first-tape-rewinding configuration, the machine enters the next-tape-rewinding state. The tape contents remain unchanged, the input head stays at $P$, the auxiliary heads are at $0,z_1-1,z_2$, and the output is empty.

**Proof.** Induct on $j$. When $j=0$, the first auxiliary head is at $-1$, so `Turing.FinTM.bufferTape_left` gives a blank reading. The run-successor law (`Turing.MultiTapeTM.runFrom_succ_eq_step`) and zero-step law (`Turing.MultiTapeTM.runFrom_zero`) reduce the claim to one step. The configuration-specific step formula (`Complexity.Meyer.acfg_step`) and the auxiliary read fact (`Complexity.Meyer.aux_read0`) identify the blank branch: the machine enters the next-tape-rewinding state and moves the first auxiliary head right. By the action-on-auxiliary-tapes formula (`Complexity.Meyer.tact_idle_apply`), the tape contents are unchanged, the first head moves from $-1$ to zero, the second moves from $z_1$ to $z_1-1$, and all remaining data are preserved.

For the successor case, $j+1\le |w|$ implies $j<|w|$, and the first head at $(j+1)-1=j$ reads $w[j]$ by `Complexity.Meyer.bufferTape_pred`. The transition stays in the first-tape-rewinding state and moves that head left one cell, preserving the tapes and the other data. Its new position is $j-1$, so the induction hypothesis applies to the remaining $j+1$ steps and yields the claimed next-tape-rewinding configuration. With the initial step, the total is $(j+1)+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Complexity.Meyer.acfg_step`, `Complexity.Meyer.aux_read0`, `Turing.FinTM.bufferTape_left`, `Complexity.Meyer.tact_idle_apply`, `Complexity.Meyer.bufferTape_pred`.

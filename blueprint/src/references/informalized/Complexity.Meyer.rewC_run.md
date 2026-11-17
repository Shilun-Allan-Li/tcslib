<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineSetup.lean :: Complexity.Meyer.rewC_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the Word Tape

**Claim.** For each $j\le |w|$, after $j+1$ steps from the stated rewinding configuration, the machine is in the next rewinding state, with the middle auxiliary head at zero and the third auxiliary head at $z_2-1$; the tape contents, other specified heads, input-head position, and empty output are preserved.

**Proof.** Induct on $j$. At $j=0$, the middle head starts at $-1$, so `bufferTape_left` says it reads blank. The run-successor law (`Turing.MultiTapeTM.runFrom_succ_eq_step`) and zero-step law (`Turing.MultiTapeTM.runFrom_zero`) reduce the claim to one transition. The configuration-specific step formula (`Complexity.Meyer.acfg_step`) and the auxiliary read fact (`Complexity.Meyer.aux_read1`) identify the transition's scanned symbol. The rewinding state sees blank, moves the middle head right, moves the third head left, and enters the next rewinding state. The auxiliary-action formula (`Complexity.Meyer.tact_idle_apply`) shows that the tapes are otherwise unchanged; the middle head advances from $-1$ to zero and the third from $z_2$ to $z_2-1$.

For the successor case, $j+1\le |w|$ implies $j<|w|$. The head at $(j+1)-1=j$ therefore scans $w[j]$, by `Complexity.Meyer.bufferTape_pred`, so the machine remains in the current rewinding state and moves the middle head left. The update affects only that head position: the head becomes $j-1$, the third head stays at $z_2$, and all tape contents and the other data remain fixed. Applying the induction hypothesis to the resulting configuration with parameter $j$ completes the remaining $j+1$ steps, giving the stated target. Together with the first transition this is $(j+1)+1$ steps.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Complexity.Meyer.acfg_step`, `Complexity.Meyer.aux_read1`, `Turing.FinTM.bufferTape_left`, `Complexity.Meyer.tact_idle_apply`, `Complexity.Meyer.bufferTape_pred`.

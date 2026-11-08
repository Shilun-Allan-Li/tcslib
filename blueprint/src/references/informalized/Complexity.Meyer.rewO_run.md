<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineSetup.lean :: Complexity.Meyer.rewO_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding an Auxiliary Tape

**Claim.** For each $j\le |w|$, after $j+1$ steps from the stated output-rewind configuration, the machine reaches the decode state with the initial state of $M$, empty output register, and true tag; the input position, tape contents, first two auxiliary head positions, and output are preserved, while the third auxiliary head is at zero.

**Proof.** Induct on $j$. At $j=0$, the third head is at $-1$ and reads blank by `Turing.FinTM.bufferTape_left`. The run-successor and zero-step laws (`Turing.MultiTapeTM.runFrom_succ_eq_step` and `Turing.MultiTapeTM.runFrom_zero`), followed by the configuration-specific step formula (`Complexity.Meyer.acfg_step`), reduce the claim to the blank branch of the output-rewind transition. The auxiliary read fact (`Complexity.Meyer.aux_read2`) identifies the scanned symbol; the transition enters the decode state and moves the third head right. The action-on-auxiliary-tapes formula (`Complexity.Meyer.tact_idle_apply`) shows that the other tape data and output are unchanged, and the third head moves from $-1$ to zero.

For the successor case, $j+1\le |w|$ gives $j<|w|$, and the head at $(j+1)-1=j$ reads $w[j]$ by `Complexity.Meyer.bufferTape_pred`. The transition therefore stays in the output-rewind state and moves the third head one cell left, leaving the other data fixed. The configuration-specific action formula records these changes; the resulting third-head position is $j-1$. The induction hypothesis then applies to the remaining run, with parameter $j$, and yields the desired decode configuration after those $j+1$ steps. Including the first transition gives the required $j+2$ steps, which is $(j+1)+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Complexity.Meyer.acfg_step`, `Complexity.Meyer.aux_read2`, `Turing.FinTM.bufferTape_left`, `Complexity.Meyer.tact_idle_apply`, `Complexity.Meyer.bufferTape_pred`.

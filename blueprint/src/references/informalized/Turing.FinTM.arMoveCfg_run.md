<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arMoveCfg_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Running the Move Sweep

**Claim.** For each $r\le N+1$, running the simulator for $r+1$ steps from the move-sweep configuration at counter $r$ reaches the encoding of the action-applied configuration.

**Proof.** Use induction on $r$. At $r=0$, the claim is exactly the completion-of-the-move-sweep result (`Turing.FinTM.arMoveCfg_finish`). For the successor case, write the run of $r+1$ steps as one simulator step followed by a run of $r$ steps (`Turing.MultiTapeTM.runFrom_succ_eq_step`). Since the current counter is nonzero, that first step lowers it by one and leaves the configuration in the corresponding move-sweep form (`Turing.FinTM.arMoveCfg_step`). The induction hypothesis applies to this lower counter, proving that the remaining $r$ steps reach the encoded action-applied configuration.

**Key facts.** `Turing.FinTM.arMoveCfg_finish`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.FinTM.arMoveCfg_step`.

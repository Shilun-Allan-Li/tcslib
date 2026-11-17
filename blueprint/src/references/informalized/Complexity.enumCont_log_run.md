<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_log_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lockstep simulation with a complete history

**Claim.** For every initial configuration and every time $t$, the logging machine's run from the empty-history encoding equals the encoding of the source machine's configuration at time $t$ together with the history recorded during those $t$ steps.

**Proof.** Induct on $t$. At time zero both sides are the initial configuration encoded with empty history. For the successor step, the run-iteration identity (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) reduces the logging run to one transition after the induction hypothesis. Let $c$ be the source configuration at time $t$. Its scanned work symbols, read from the source-tape block of the encoded configuration, are exactly those of $c$. If $c$ is already halted, both machines remain at the same encoded configuration and the history does not change. If its state is $q$, the logging machine uses the source transition at $q$ with those same scanned symbols. The one-step logging identity (`Complexity.enumCont_log_apply`) says that this action produces the encoding of the source configuration after that transition and appends the scanned symbols and prescribed head movements to the history. By the definition of the history, this is exactly the history at time $t+1$, completing the induction.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.enumCont_log_apply`.

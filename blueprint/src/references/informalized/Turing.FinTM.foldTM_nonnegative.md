<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean :: Turing.FinTM.foldTM_nonnegative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Heads in the Folding Simulator

**Claim.** For every folded-alphabet input, every number of steps, and every work tape, the corresponding work-head position in the folding simulator's run from its initial configuration is nonnegative.

**Proof.** Proceed by induction on the number of steps. At zero steps, each work head starts at position zero, hence is nonnegative. For a positive number of steps, first prove by induction on $t$ that the configuration reached after one initial step and then $t$ further steps satisfies the safety invariant. The base case is the initialization safety result (`foldSafe_init`); the induction step follows because one simulator step preserves safety (`foldSafe_step`). A run after $t+1$ steps is the run after one initial step followed by $t$ further steps (`runFrom_succ_eq_step`). Its safety invariant includes nonnegativity of every work-head position, giving the claim.

**Key facts.** `Turing.FinTM.foldSafe_init`, `Turing.FinTM.foldSafe_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.

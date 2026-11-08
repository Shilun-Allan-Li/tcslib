<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_budget_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding to Budget Origin

**Claim.** Starting in budget-start phase with the budget head at $|w|+1$, after $|w|+2$ steps the machine is in append phase with its budget head at cell $1$, while the other data and tapes are unchanged.

**Proof.** The first budget-start transition changes phase to budget-back and moves the budget head one cell left. The action on the setup configuration is computed using `setupCfg_apply`. The remaining $|w|+1$ steps are exactly the budget-back traversal from coordinate $|w|$; `setupCfg_budget_back` shows that this reaches append phase at cell $1$ while preserving the clock tape and all other setup data. The run successor law composes the initial step with that traversal.

**Key facts.** `Complexity.setupCfg_apply`, `Complexity.setupCfg_budget_back`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.

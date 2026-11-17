<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_budget_back -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the Budget Head

**Claim.** Starting in budget-back phase with the budget head at cell $j$, the machine reaches append phase with its budget head at cell $1$ after $j+1$ steps, preserving the other configuration data and the captured clock tape.

**Proof.** At a budget-back configuration with head coordinate $j$, the symbol under the head is the clock-tape origin exactly when $j=0$ (`clockTape_origin`). The transition therefore enters append phase and moves the head to cell $1$ in that case; if $j>0$, it stays in budget-back phase and moves one cell left. The action on the setup configuration is expressed by `setupCfg_apply`, which records that this transition changes only the specified phase and head position. Induct on $j$: at zero the single step reaches the stated append configuration, and at a successor the first step reduces the head coordinate by one, after which the induction hypothesis accounts for the remaining steps. The run-from zero and successor laws identify these iterated steps with the claimed run of length $j+1.

**Key facts.** `Complexity.clockTape_origin`, `Complexity.setupCfg_apply`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.

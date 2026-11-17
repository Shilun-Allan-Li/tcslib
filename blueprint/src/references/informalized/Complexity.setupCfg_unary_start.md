<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_unary_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Counter Initialization

**Claim.** Starting in unary-start phase with unary head at $N+1$ and $N$ markers on the unary tape, after $N+2$ steps the machine is in the first rightward layout phase with unary head at $1$, leaving all other configuration data unchanged.

**Proof.** The first transition from unary-start enters the nonterminal unary-rewind phase, moves the unary head left from $N+1$ to $N$, and changes no tape contents. This follows by applying the setup-configuration update rule (`setupCfg_apply`). The remaining $N+1$ steps are exactly the unary-rewind run with parameter $j=N$ and `last` false: it reaches the first rightward layout phase with head at $1$, by `setupCfg_unary_rewind`. The successor-step law for runs (`Turing.MultiTapeTM.runFrom_succ_eq_step`) combines this first transition with those remaining steps.

**Key facts.** `Complexity.setupCfg_apply`, `Complexity.setupCfg_unary_rewind`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.

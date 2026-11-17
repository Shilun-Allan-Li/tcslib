<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_lift_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symbol Lifting Commutes with Execution

**Claim.** For every number of steps, running the symbol-lifted decrement machine from a configuration over $\Gamma$ agrees with decoding that configuration, running the Boolean decrement machine, and lifting the resulting run back over the original configuration.

**Proof.** The lifting operation applied to the decoded configuration recovers the original configuration (`Cfg.liftOver_decodeSymbols`), so rewrite the initial configuration in this form. The run-commutation theorem for lifted machines (`MultiTapeTM.liftSymbols_runFrom_over`) then applies: the decrement transition ignores the input symbol (`decrementTM_tr_input`), and its actions never attempt to write an undefined symbol (`decrementTM_tr_action`). Consequently, at every step the lifted transition agrees with decoding the observed symbols, performing the Boolean transition, and re-encoding its writes. Iterating this compatibility for $t$ steps gives the stated equality of configurations.

**Key facts.** `Turing.Cfg.liftOver_decodeSymbols`, `Turing.decrementTM_tr_input`, `Turing.decrementTM_tr_action`, `Turing.MultiTapeTM.liftSymbols_runFrom_over`.

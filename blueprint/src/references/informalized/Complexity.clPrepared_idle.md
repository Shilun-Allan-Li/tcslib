<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clPrepared_idle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stationarity of a Prepared Machine State

**Claim.** If the transition from a state $r$ of the simulated machine is always the stationary control action returning to $r$, then every prepared-machine configuration in the copied state of $r$ is unchanged by one step.

**Proof.** In the prepared machine’s simulated phase, the transition at the copied state is the placed version of the transition at $r$. By the hypothesis, that transition is the stationary control action. The placed-action identity (`Complexity.clPlacedAction_eq`) shows that placement leaves the input movement, output, and successor-state behavior as prescribed, while every host work tape either receives the corresponding source action or is left untouched. Since the source action writes nothing and moves no head, the placed action also writes nothing and moves no head. It is therefore exactly the stationary control action at the copied state. Applying it leaves the configuration unchanged: the control-action effect is `Turing.FinTM.controlAction_apply`, and its zero input movement fixes the input position (`Turing.moveInputPos_zero`).

**Key facts.** `Complexity.clPlacedAction_eq`, `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.

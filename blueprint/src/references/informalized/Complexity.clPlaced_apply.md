<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clPlaced_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Action on a placed configuration

**Claim.** Applying the placed version of a source action to the placed version of a source configuration yields the placement of the configuration obtained by applying the source action.

**Proof.** Consider the constant source machine whose transition is the given action $a$. Running its embedded machine for one step from the embedded configuration performs exactly that transition while keeping the unoccupied host tapes framed; the one-step embedding identity (`Turing.embedEmitTM_runFrom`) expresses the result as the embedding of the source configuration after one step. Expanding that one-step transition identifies it with applying $a$ to $c$. Finally, mapping the states commutes with applying an action (`Turing.Cfg.mapState_apply`), so the resulting equality is precisely the asserted identity for placed actions and configurations.

**Key facts.** `Turing.embedEmitTM_runFrom`, `Turing.Cfg.mapState_apply`.

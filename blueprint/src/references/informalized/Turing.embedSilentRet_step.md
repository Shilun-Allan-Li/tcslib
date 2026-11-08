<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedSilentRet_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One step of the silent return machine

**Claim.** If $c$ has a present state, one step of the return machine from the embedded configuration with its state mapped into the left summand equals the return-state embedding of the configuration obtained by one step of $M$ from $c$.

**Proof.** First use the general return-step correspondence (`Turing.embedReturn_step`) for the silent embedding of $M$ and its return machine. Since $c$ has a present state, the embedded configuration is equal to the configuration obtained by mapping its state into the left summand (`Turing.embedReturnCfg_live`). The silent embedding also commutes with one step of the original machine (`Turing.embedSilent_step`). Substituting these two identities into the general correspondence gives the claimed equality.

**Key facts.** `Turing.embedReturnCfg_live`, `Turing.embedReturn_step`, `Turing.embedSilent_step`.

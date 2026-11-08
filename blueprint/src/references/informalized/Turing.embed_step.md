<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean :: Turing.embed_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedding a Single Machine Step

**Claim.** If the source configuration is in state $q$ and the host transition at $b$ is the padded, state-mapped action prescribed by the source transition at $q$, then a host step from the embedded configuration with state replaced by $b$ equals the embedding of the source machine's one-step result.

**Proof.** The input head position is unchanged by embedding, so the two configurations scan the same input symbol. On each of the original $m$ tapes, the embedded configuration scans exactly the symbol scanned by the source configuration (`Turing.embedCfg_workTapeSymbols`). The host transition hypothesis therefore identifies its action with the padded source action. Applying that padded action to the modified embedded configuration gives the embedding of the source action applied to the original configuration (`Turing.padAction_apply`). Finally, because the source state is $q$, its machine step is exactly the application of its transition at $q$ to the source configuration. These identifications yield the claimed equality.

**Key facts.** `Turing.embedCfg_workTapeSymbols`, `Turing.padAction_apply`.

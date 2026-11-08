<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clPlaced_release -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step simulation from a release state

**Claim.** If the host machine's transition from the release state is the placed source action on the source state and the symbols read at the placed tape indices, then one host step from the release-state placement of $c$ equals the placement of the source machine's next configuration.

**Proof.** At each source tape index $i$, the host tape at the corresponding placed index has exactly the source tape's contents, and its head is at the source head position. These selected-tape and selected-position facts (`Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`) imply that the source machine reads the same work-tape symbols from $c$ as the host reads at the placed indices. The input symbol also agrees because placement preserves the input-head position. The assumed transition equation therefore makes the host's release-state transition the placed version of the source transition at $q$. Applying the compatibility of placed actions with placed configurations (`Complexity.clPlaced_apply`), and using $c$'s state hypothesis to identify the source step with that transition, gives the claimed one-step equality.

**Key facts.** `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`, `Complexity.clPlaced_apply`.

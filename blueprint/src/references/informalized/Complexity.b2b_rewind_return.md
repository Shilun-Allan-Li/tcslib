<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_rewind_return -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewind Return to the Left Boundary

**Claim.** The embedded rewind machine reaches the configuration whose state is the return state and whose input-head position is $1$, with every other configuration field as in the original configuration. It does not reach the return state earlier, and its work-head positions agree with the original throughout the run.

**Proof.** The rewind-run theorem (`Complexity.b2b_rewind_run`) supplies a time $r$ when the original machine halts at input position $1$, while preserving all work-head positions through time $r$. Take the first halting time $T$ of this run using `Turing.MultiTapeTM.exists_first_halt`. Its terminal configuration is unchanged, and the original machine is live at all earlier times. The embedding simulation theorem (`Turing.embedEmitRetTM_run`) therefore matches the embedded machine to the original run before $T$ and places it in the return state at $T$. The identity-embedding configuration lemma (`Complexity.b2b_embed_refl`) identifies the initial embedded configuration with the original one. Before $T$, the work-head positions consequently agree by the simulation and the bound through $r$; at $T$, they agree because the terminal configuration is the same as at time $r$.

**Key facts.** `Complexity.b2b_rewind_run`, `Turing.MultiTapeTM.exists_first_halt`, `Turing.embedEmitRetTM_run`, `Complexity.b2b_embed_refl`.

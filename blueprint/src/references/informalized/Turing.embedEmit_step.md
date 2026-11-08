<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedEmit_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step of an embedded machine

**Claim.** One step of the embedded machine from an embedded configuration is the embedding of the original machine's one-step result, with the same initial contents, head positions, and output prefix.

**Proof.** Unfold the one-step transition and split on the state of the original configuration. If it is halted, both machines stay at their respective configurations, and the result follows from the definition of the embedding. If the state is $q$, the embedded configuration has state $q$ as well. Its input symbol is unchanged, and its work-head symbols at each selected index agree with those of the original configuration: the embedding selects the corresponding original tape (`embedSlot_selected`). Thus the embedded machine consults exactly the same transition as the original machine. The action-respecting-embedding lemma (`embedEmit_apply`) then identifies the resulting configuration with the embedding of the original one-step result.

**Key facts.** `Turing.embedEmit_apply`, `Turing.embedSlot_selected`.

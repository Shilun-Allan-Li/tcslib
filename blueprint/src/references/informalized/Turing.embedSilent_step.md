<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedSilent_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Simulation Under Silent Embedding

**Claim.** One step of the silently embedded machine from the silent embedding of $c$ equals the silent embedding of the configuration reached by one step of $M$.

**Proof.** Unfold the definition of a machine step and split according to whether $c$ is halted. If its state is absent, both machines leave the configuration unchanged, so the desired equality follows directly. If its state is $q$, the embedded configuration has the same state and input symbol. Moreover, at every embedded tape index $\iota(i)$ its head symbol is the one on tape $i$ of $c$, because the selected slot there is exactly $i$ (\texttt{embedSlot\_selected}). Thus the transition of the embedded machine is the embedded action corresponding to the transition of $M$ on the same state and tape symbols. Applying the action-commutation result (\texttt{embedSilent\_apply}) identifies the resulting configuration with the embedding of $M$'s one-step result.

**Key facts.** `Turing.embedSlot_selected`, `Turing.embedSilent_apply`.

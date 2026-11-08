<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedSilentTM_runFrom -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run commutes with silent embedding

**Claim.** Running the silent embedding for $t$ steps from the embedded configuration gives exactly the embedding of the configuration reached by running $M$ for $t$ steps from $c$.

**Proof.** The one-step correspondence `Turing.embedSilent_step` states that applying the silent machine's step to an embedded configuration equals embedding the result of one step of $M$. The general iteration principle (`Turing.MultiTapeTM.runFrom_comm_of_step`) says that whenever a map preserves one-step evolution, it also intertwines runs for every natural number of steps. Apply it to the configuration embedding and this one-step identity to obtain the equality at time $t$.

**Key facts.** `Turing.MultiTapeTM.runFrom_comm_of_step`, `Turing.embedSilent_step`.

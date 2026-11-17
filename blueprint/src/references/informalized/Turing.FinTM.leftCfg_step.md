<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.leftCfg_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step simulation under left-block embedding

**Claim.** Under the stated transition compatibility, one step of the extended machine from the embedded configuration equals the embedding of one step of the original machine.

**Proof.** Unfold the one-step transition and split on the original configuration's state. If it is halting, both machines leave their configurations unchanged, and the claimed equality follows directly. If the state is $q$, the embedded configuration has state $f(q)$. The transition compatibility hypothesis identifies the extended machine's action there with the left-block extension of the original transition action. Its first $k$ scanned tape symbols agree with those in the original configuration, since the embedding preserves the first block of tapes and their head positions. Finally, applying the extended action to the embedded configuration agrees with embedding the result of applying the original action (`Turing.FinTM.leftCfg_apply`).

**Key facts.** `Turing.FinTM.leftCfg_apply`.

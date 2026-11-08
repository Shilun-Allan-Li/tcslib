<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.rightCfg_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Simulation on the Right Block

**Claim.** Under the stated transition compatibility, one step of the larger machine from the right-block embedding equals the embedding of one step of the smaller machine, preserving the first-block tape data.

**Proof.** Unfold the definition of a machine step and split on the original configuration's state. If it is halted, both machines leave their configurations unchanged, and the embedding preserves that equality. If its state is $q$, the embedded state is $f(q)$. The transition hypothesis identifies the larger machine's transition there with the right-block extension of the smaller transition. Moreover, the symbols read on the embedded configuration's last $l$ tapes are exactly the symbols read on the original configuration: the right block of the embedded tapes and head positions is the original tape data. Applying the action-embedding identity (`rightCfg_apply`) then gives the required equality of configurations.

**Key facts.** `Turing.FinTM.rightCfg_apply`.

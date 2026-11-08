<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.rightCfg_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lockstep Run on the Right Block

**Claim.** If the larger machine's transitions are the right-block extensions of the smaller machine's transitions, then its run from the embedded configuration for $t$ steps is the embedding of the smaller machine's run, with the first-block tape data fixed.

**Proof.** Use the step-by-step simulation for right-block configurations (`rightCfg_step`): at every configuration, one step of the larger machine equals the embedding of one step of the smaller machine. The general run-commutation result (`runFrom_comm_of_step`) lifts this equality from a single step to any number $t$ of steps. Apply it to the embedding that places the original configuration on the last $l$ tapes and uses the chosen contents and head positions on the first $k$ tapes.

**Key facts.** `Turing.FinTM.rightCfg_step`, `Turing.MultiTapeTM.runFrom_comm_of_step`.

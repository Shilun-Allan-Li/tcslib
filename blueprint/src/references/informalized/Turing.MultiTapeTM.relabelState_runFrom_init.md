<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/StateRenaming.lean :: Turing.MultiTapeTM.relabelState_runFrom_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relabelled Initial Runs

**Claim.** Relabelling the states of a machine commutes with running it for any number of steps from its initial configuration.

**Proof.** Apply the general principle that a map commuting with one-step transitions also commutes with every finite run (`runFrom_comm_of_step`). Here the map sends a configuration to the same configuration with its state relabelled by $e$. The one-step compatibility required by that principle is exactly the fact that relabelling commutes with a step (`relabelState_step`). Finally, the relabelled machine’s initial configuration is the image under this map of the original initial configuration, since its initial state is $e(q_0)$ and all other configuration data agree. Substituting these facts gives the claimed equality.

**Key facts.** `Turing.MultiTapeTM.relabelState_step`, `Turing.MultiTapeTM.runFrom_comm_of_step`.

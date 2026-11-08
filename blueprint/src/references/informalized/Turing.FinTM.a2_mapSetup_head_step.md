<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_mapSetup_head_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Setup preserves simulated tape heads

**Claim.** During a setup step of the mapping machine in non-forward mode, the head on each tape representing a work tape of $M$ remains at the same position.

**Proof.** If the configuration is halted, stepping leaves it unchanged. Otherwise inspect the transition according to its state. In every setup state—parsing, copying, rewinding, or emitting—the transition leaves each simulated tape's movement equal to zero. In the run state, non-forward mode uses a control action, which also gives zero movement on those tapes. The tape-block indexing fact identifies the simulated tape among the right-hand block of tapes (`tapeBlocks_right`). Since a step adds the selected movement to each head position, zero movement leaves the position unchanged.

**Key facts.** `Turing.FinTM.tapeBlocks_right`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineRun.lean :: Complexity.Meyer.dec_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Cell Counter Update

**Claim.** If the counter tape contains false at its current head, one step of the tabulating machine retains the simulated decode configuration, writes true at that counter cell, advances the counter head by one, and leaves the other specified data unchanged.

**Proof.** The lifted-configuration step formula reduces the simulator step to its tabulated transition applied to the current configuration (`lcfg_step`). In the decode state, the transition reads the counter symbol from auxiliary tape 1 (`aux_read1`); by hypothesis that symbol is false, so the transition takes the branch that writes true there, moves that auxiliary head one position right, and leaves the other tapes and simulated data alone. The auxiliary-action formula converts this action into the resulting lifted configuration (`lcfg_apply_aux`), which is exactly the asserted update.

**Key facts.** `Complexity.Meyer.lcfg_step`, `Complexity.Meyer.aux_read1`, `Complexity.Meyer.lcfg_apply_aux`.

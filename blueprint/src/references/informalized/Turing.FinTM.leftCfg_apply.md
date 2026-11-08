<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.leftCfg_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Action application under left-block embedding

**Claim.** Applying the extended action to the left-block embedding gives the embedding of the original action's result, with the additional tapes unchanged.

**Proof.** Configurations are equal once their state, input-head position, tape contents, tape-head positions, and output agree. The state and output agree directly: both are obtained by renaming the original state and preserving the original output. The input-head movement is also the same. For tape contents, split the indices into the first $k$ tapes and the additional $l$ tapes. On a first-block tape, both sides apply the same write-or-preserve operation at the same head position to the same original tape. On an additional tape, the extended action prescribes no write and zero movement, so its contents and head position remain the chosen ones. Thus every configuration component agrees.

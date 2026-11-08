<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.rightCfg_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Action on the Right Block

**Claim.** Applying the extended action to a configuration embedded in the right block gives the embedding of the action's result, with the first $k$ tapes' contents and head positions preserved.

**Proof.** Configurations agree in their state, input position, output, tape contents, and work-head positions. The state and output agree directly, and both sides have the same input-head movement. For tape contents and head positions, split the tape index into the first block and the last block, using the decomposition of indices into left and right cases. In the first block the extended action writes nothing and moves no head, so the original contents and positions are retained. In the last block it applies exactly the action on the original configuration. Thus all components agree.

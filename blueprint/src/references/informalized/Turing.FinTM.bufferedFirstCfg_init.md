<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.bufferedFirstCfg_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initialization of Buffered Composition

**Claim.** The initial configuration of the buffered sequential composition on $x$ equals the first-phase configuration embedding of $M_1$'s initial configuration on $x$.

**Proof.** Compare the configuration fields. The state, input-head position, and output agree directly: both start in the first machine's initial state, at the same input position, with empty output. For the work tapes and their head positions, split the composite tape index into the left block, the single buffer tape, and the right block. On the left block the embedded configuration copies $M_1$'s initial data; on the buffer tape the empty output gives an empty buffer and its head position is zero; on the right block the tapes are blank and their heads start at zero. These agree with the composite machine's initial work tapes and head positions, so the configurations are equal.

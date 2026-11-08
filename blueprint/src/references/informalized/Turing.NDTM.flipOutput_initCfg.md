<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTM.lean :: Turing.NDTM.flipOutput_initCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial configuration and flipped output

**Claim.** The initial configuration of the machine that flips output symbols is the configuration obtained by flipping every output bit in the original machine's initial configuration.

**Proof.** Both initial configurations have the initial state, the initial input-head position, blank work tapes, and work-tape heads at the origin. Their outputs are empty; flipping each bit of the empty output leaves it empty. Thus the two configurations agree in every component.

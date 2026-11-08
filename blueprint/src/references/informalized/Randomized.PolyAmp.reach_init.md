<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean :: Randomized.PolyAmp.reach_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Configuration Reachability

**Claim.** The initial configuration is reachable from itself in the sense that some choice word produces a configuration with the same machine core and output summary.

**Proof.** Choose the empty choice word. Running the machine on no choices leaves the initial configuration unchanged, so its core and output summary agree with those of the initial configuration by reflexivity.

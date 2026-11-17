<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.cont -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability Under Equal Initial States

**Claim.** If two register states are equal, any guarded finite run from the configuration using the second state is also a guarded finite run from the otherwise identical configuration using the first state.

**Proof.** The hypothesis identifies the two register states. Rewriting the initial configuration along this equality makes it exactly the configuration from which the given guarded reachability run starts. The same run length, endpoint, and guard conditions therefore witness the desired reachability.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine.lean :: Complexity.PathHard.cont -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuation Under Equal Registers

**Claim.** If two register records are equal, any guarded reachability run starting from the second record also gives the same run starting from the first record, with the same label and endpoint.

**Proof.** The equality of register records induces equality of their register vectors, since each vector is obtained by applying the same register-to-vector map. Transport the given reachability statement along the assumed equality of records; the label, endpoint, oracle, and guard are unchanged.

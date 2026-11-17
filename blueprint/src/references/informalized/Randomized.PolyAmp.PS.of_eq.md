<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.PS.of_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Record Invariance

**Claim.** If two register records are equal, the polynomial-amplification program has the same termination and probability properties when started from either record.

**Proof.** The hypothesis identifies the two records, so their encoded register vectors agree and the initial configurations at label $l$ are equal. The property asserting termination and the specified probabilities is therefore unchanged. Formally, equality substitution transports the assumed semantic property directly to the configuration initialized with the other record.

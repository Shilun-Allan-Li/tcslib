<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UPS.of_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance Under Equal Register Records

**Claim.** If two register records are equal, any stated probabilistic semantics property for the initial configuration formed from the second also holds for the initial configuration formed from the first.

**Proof.** The hypothesis identifies the two register records. Rewriting the initial configuration using this equality makes it identical to the initial configuration in the assumed semantics property. Hence that property transfers directly to the first record.

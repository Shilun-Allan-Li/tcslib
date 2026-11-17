<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Run.lean :: Complexity.LogProg.SavitchARM.cont -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution Under Equal States

**Claim.** If the two register states are equal, any finite safe bounded execution from one state is also such an execution from the other to the same final configuration.

**Proof.** The equality of states identifies their register vectors, so the two initial configurations—with the same label and no answer—are equal. Replacing the initial configuration in the given reachability witness by an equal one leaves the entire iterated execution, its endpoint, and every safety and register-bound condition unchanged.

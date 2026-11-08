<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.toV_C -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Loop counter coordinate

**Claim.** For every machine state, the register-vector coordinate indexed by the loop counter equals the loop counter register.

**Proof.** The register vector lists the loop counter as its seventh entry, and the loop-counter index is the index of that entry. Selecting it therefore returns the loop counter register itself.

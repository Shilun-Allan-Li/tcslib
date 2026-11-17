<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.toV_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Register Vector

**Claim.** The register vector of the all-zero state is the function that assigns zero to every register index.

**Proof.** Two functions on the 18 register indices are equal if they agree at each index. Check the indices one by one: each value in the register vector of the zero state is zero, matching the constant-zero function. Thus the functions agree everywhere.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.toV_a -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Base Register Coordinate

**Claim.** For any register state, the coordinate of its register vector at the base-register index is the state's base register.

**Proof.** The register vector lists the state coordinates in order, placing $a$ at index $1$. The base-register index is $r_a=1$, so the vector's value there is $a$.

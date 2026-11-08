<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.toV_w -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Code Width Coordinate

**Claim.** For any register state, the coordinate of its register vector at the code-width index is the state's code width.

**Proof.** The register vector lists the state coordinates in order, placing $w$ at index $8$. The code-width index is $r_w=8$, so the vector's value there is $w$.

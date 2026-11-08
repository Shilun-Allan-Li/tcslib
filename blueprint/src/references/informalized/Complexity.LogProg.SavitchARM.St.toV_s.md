<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.toV_s -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Window Radius Coordinate

**Claim.** For any register state, the coordinate of its register vector at the window-radius index is the state's window radius.

**Proof.** The register vector lists the state coordinates in order, placing $s$ at index $7$. Since the window-radius index is $r_s=7$, the value of the vector at that index is $s$.

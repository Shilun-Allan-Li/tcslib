<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.toV_k -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Add-twice counter coordinate

**Claim.** For any state σ whose 17-coordinate encoding lists its fields in order, the coordinate at index 2 is the add-twice counter k.

**Proof.** The ordered register vector places σ.k in position 2, with indices starting at 0. The designated coordinate rk is 2, so evaluating the vector there yields σ.k.

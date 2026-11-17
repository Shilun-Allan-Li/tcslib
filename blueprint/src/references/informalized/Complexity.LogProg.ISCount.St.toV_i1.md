<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.toV_i1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stage-plus-one coordinate

**Claim.** For any state σ, the 17-entry encoding lists its fields in order, and its coordinate at index 8 is the stage-plus-one field i₁.

**Proof.** In the ordered register vector, σ.i₁ occupies position 8 when indexing starts at 0. Because ri1 is 8, the value at that coordinate is σ.i₁ by direct evaluation.

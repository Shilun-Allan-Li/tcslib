<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.toV_i -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stage coordinate

**Claim.** For any state σ and natural number z, the register vector associated with σ has value i at coordinate 7.

**Proof.** The register vector lists σ.i in position 7, with indexing starting at 0. Since ri is 7, evaluating the vector at that coordinate gives σ.i directly, independently of z.

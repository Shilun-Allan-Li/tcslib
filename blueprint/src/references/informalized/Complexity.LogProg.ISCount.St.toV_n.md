<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.toV_n -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-length coordinate

**Claim.** For any state σ whose 17-coordinate encoding lists its fields in order, the coordinate at index 0 is the input length n.

**Proof.** The first entry of the ordered register vector is σ.n, and its index is 0. Since rn is 0, evaluating the vector at rn gives σ.n directly.

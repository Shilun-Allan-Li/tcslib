<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.v_1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vertex Count Slot

**Claim.** For any register state, slot $1$ of its register vector contains its vertex count.

**Proof.** The register-value vector lists the state’s fields in register order, with the vertex count in position $1$. Evaluating the vector at that position gives the vertex count.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.toV_v -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outer-vertex coordinate

**Claim.** For any state $\sigma$, the coordinate at index $10$ of its 17-coordinate encoding is the outer vertex $v$.

**Proof.** By definition, the encoding lists the state fields in order, with $v$ in position $10$. Evaluating the encoding at that index therefore returns $v$.

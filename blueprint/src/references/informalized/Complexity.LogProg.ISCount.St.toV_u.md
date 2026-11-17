<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.toV_u -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner-vertex coordinate

**Claim.** For any state $\sigma$, the coordinate at index $12$ of its 17-coordinate encoding is the inner vertex $u$.

**Proof.** By definition, the encoding lists the state fields in order, with $u$ in position $12$. Evaluating the encoding at that index therefore returns $u$.

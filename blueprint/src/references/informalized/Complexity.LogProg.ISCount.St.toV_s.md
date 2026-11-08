<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.toV_s -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Window-radius coordinate

**Claim.** For any state $\sigma$, the coordinate at index $3$ of its 17-coordinate encoding is the window radius $s$.

**Proof.** By definition, the encoding lists the state fields in order, with $s$ in position $3$. Evaluating the encoding at that index therefore returns $s$.

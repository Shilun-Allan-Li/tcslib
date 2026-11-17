<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.St.toV_V -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Current Variable Coordinate

**Claim.** For every state, the coordinate of its register vector indexed by the current-variable register is equal to the value of that register.

**Proof.** The register vector lists the state fields in order, with the current-literal variable $V$ in position $6$. Since $rV=6$, evaluating the vector there returns $V$.

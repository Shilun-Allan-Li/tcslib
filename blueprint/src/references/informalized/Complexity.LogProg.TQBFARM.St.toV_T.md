<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.St.toV_T -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scratch Copy Coordinate

**Claim.** For every state, the coordinate of its register vector indexed by the scratch copy register is equal to the value of that register.

**Proof.** The register vector lists the state fields in order, with the scratch copy $T$ in position $3$. Since $rT=3$, evaluating the vector there returns $T$.

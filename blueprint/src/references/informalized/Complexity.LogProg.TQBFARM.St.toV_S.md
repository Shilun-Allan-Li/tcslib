<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.St.toV_S -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Assignment Stack Coordinate

**Claim.** For every state, the coordinate of its register vector indexed by the assignment stack is equal to the value of its assignment stack.

**Proof.** The register vector lists the state fields in order, with the assignment stack in position $1$. Since $rS=1$, evaluating the vector at that index gives the second listed field, namely $S$.

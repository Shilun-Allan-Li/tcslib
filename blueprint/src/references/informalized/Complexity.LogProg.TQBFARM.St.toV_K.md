<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.St.toV_K -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth Coordinate

**Claim.** For every state, the coordinate of its register vector indexed by the depth register equals the value of its depth register.

**Proof.** The encoded vector lists the registers in order, with the depth register $K$ at index $0$. The coordinate indexed by the depth-register index is therefore $K$.

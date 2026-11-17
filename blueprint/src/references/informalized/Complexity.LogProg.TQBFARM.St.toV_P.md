<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.St.toV_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Pointer Coordinate

**Claim.** For every state, the coordinate of its register vector indexed by the input pointer equals the value of its input pointer.

**Proof.** The encoded vector lists the registers in order, with the input pointer $P$ at index $2$. Hence the coordinate at the input-pointer index is $P$.

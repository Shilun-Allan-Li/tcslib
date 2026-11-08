<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.St.toV_C -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scratch Counter Coordinate

**Claim.** For every state, the coordinate of its register vector indexed by the counter register equals the value of its counter register.

**Proof.** The encoded vector lists the registers in order, with the counter $C$ at index $5$, which is precisely the counter-register index. Thus that coordinate is $C$.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonSearchFamily.lean :: BoolCircuit.DAGCircuit.rewire_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewiring preserves fan-in two

**Claim.** If $C$ has distinct input vertices at every gate, exactly one input at each NOT gate, and at most two inputs at every gate, then its rewired circuit has those same properties.

**Proof.** Every gate in the rewired list belongs either to the initial pair of constant gates or to the embedded gates. The two constant gates have no arguments, so they have distinct arguments, satisfy the NOT-gate condition vacuously, and have at most two arguments. For each embedded gate, the fan-in preservation theorem (`faninTwo_embedGates`) gives all three properties. Hence every gate in the rewired circuit satisfies them, which is precisely the definition of fan-in two.

**Key facts.** `BoolCircuit.faninTwo_embedGates`.

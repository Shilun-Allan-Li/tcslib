<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean :: BoolCircuit.constZeroCircuit_onlyUsesGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate operations in the zero circuit

**Claim.** For every natural number $n$, the depth-two circuit from $\mathbb{R}^n$ to a singleton output uses only the identity, NOT, and unbounded fan-in AND operations on $\mathrm{Fin}\,2$.

**Proof.** Consider a gate in either of the two layers. In the first layer its operation is the AND operation with zero inputs, which belongs to the specified set of standard operations by the membership fact for AND gates (BoolCircuit.andGateOp_mem_stdGateOps). In the second layer its operation is NOT, which belongs to the same set by the membership fact for NOT (BoolCircuit.notGateOp_mem_stdGateOps). There are no further layers in a depth-two circuit, so these cases account for every gate.

**Key facts.** `BoolCircuit.andGateOp_mem_stdGateOps`, `BoolCircuit.notGateOp_mem_stdGateOps`.

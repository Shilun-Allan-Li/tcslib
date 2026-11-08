<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SizeClasses.lean :: BoolCircuit.allOnesFamily_onlyUsesGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate Set of the All-Ones Family

**Claim.** For every natural-number input length, the corresponding circuit in the all-ones family uses only the identity operation, negation, or an AND operation of finite arity.

**Proof.** Fix an input length $n$. The circuit has depth one, so every gate layer has index either $0$ or $1$. At layer $0$, its gates are the AND gate of arity $n$, which belongs to the standard gate set by the fact that every finite-arity AND gate is standard (`BoolCircuit.andGateOp_mem_stdGateOps`). Layer $1$ has no gates, since the circuit's depth is one. Thus every gate that occurs belongs to the standard gate set.

**Key facts.** `BoolCircuit.andGateOp_mem_stdGateOps`.

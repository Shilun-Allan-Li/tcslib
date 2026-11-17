<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniform.lean :: BoolCircuit.DAGCircuitFamily.IsLogspaceUniform.isPolySize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial size from logspace uniformity

**Claim.** If a circuit family is logspace-uniform, then there are natural numbers $a$ and $k$ such that $\mathrm{size}(C_n)\leq a(n+1)^k$ for every $n$.

**Proof.** Logspace uniformity implies polynomial-time uniformity, and polynomial-time uniformity implies polynomial size (BoolCircuit.DAGCircuitFamily.IsLogspaceUniform.isPUniform; BoolCircuit.DAGCircuitFamily.IsPUniform.isPolySize). Applying these two results successively to the given family yields the asserted constants $a$ and $k$.

**Key facts.** `BoolCircuit.DAGCircuitFamily.IsLogspaceUniform.isPUniform`, `BoolCircuit.DAGCircuitFamily.IsPUniform.isPolySize`.

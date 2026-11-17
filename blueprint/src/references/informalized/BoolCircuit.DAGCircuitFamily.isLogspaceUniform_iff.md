<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdj.lean :: BoolCircuit.DAGCircuitFamily.isLogspaceUniform_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniformity and adjacency characterization

**Claim.** For a canonical family of Boolean circuits, logspace uniformity is equivalent to polynomial size together with logspace decidability of its size language, each gate-type language, and its edge language.

**Proof.** The equivalence follows by applying the two characterizations in opposite directions. A logspace-uniform family has polynomial size and logspace-decidable size, gate-type, and edge languages, by the forward characterization (IsLogspaceUniform.hasLogspaceAdjacency). Conversely, if these size and language conditions hold, then the canonical family is logspace-uniform, by the reverse characterization (HasLogspaceAdjacency.isLogspaceUniform).

**Key facts.** `BoolCircuit.DAGCircuitFamily.IsLogspaceUniform.hasLogspaceAdjacency`, `BoolCircuit.DAGCircuitFamily.HasLogspaceAdjacency.isLogspaceUniform`.

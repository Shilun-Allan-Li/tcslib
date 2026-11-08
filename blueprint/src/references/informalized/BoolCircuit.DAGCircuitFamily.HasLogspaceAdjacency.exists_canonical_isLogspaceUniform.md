<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformCanon.lean :: BoolCircuit.DAGCircuitFamily.HasLogspaceAdjacency.exists_canonical_isLogspaceUniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical uniform circuit family

**Claim.** A family with logspace-decidable adjacency information and output vertex immediately preceding the end of each circuit has a canonical, logspace-uniform family computing the same Boolean functions.

**Proof.** Take the canonicalized family $C^{\mathrm{canon}}$. For each input length, the output-position hypothesis implies that its canonicalized circuit is canonical (\texttt{isCanonical\_canon}). Canonicalization preserves the computed Boolean function at each length (\texttt{eval\_canon}). It also preserves logspace-decidable adjacency information (\texttt{hasLogspaceAdjacency\_canon}). Finally, for a canonical family, logspace uniformity is equivalent to logspace-decidable adjacency information (\texttt{isLogspaceUniform\_iff}); applying this equivalence gives the desired uniformity. Thus the canonicalized family has all three asserted properties.

**Key facts.** `BoolCircuit.DAGCircuit.isCanonical_canon`, `BoolCircuit.DAGCircuit.eval_canon`, `BoolCircuit.DAGCircuitFamily.hasLogspaceAdjacency_canon`, `BoolCircuit.DAGCircuitFamily.isLogspaceUniform_iff`.

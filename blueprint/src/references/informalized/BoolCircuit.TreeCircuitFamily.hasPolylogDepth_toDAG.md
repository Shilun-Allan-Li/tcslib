<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: BoolCircuit.TreeCircuitFamily.hasPolylogDepth_toDAG -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polylogarithmic depth under DAG conversion

**Claim.** If a family of Boolean circuits has depth at most $b(\log_2 n+1)^d$ at every input length $n$, then its associated DAG circuit family satisfies a polylogarithmic depth bound with a natural-number constant.

**Proof.** Choose $b$ witnessing the assumed bound. For each $n$, the tree-to-DAG depth estimate bounds the converted circuit's depth by the original depth plus one. Apply the natural-number estimate that if $t\le b(L+1)^d$, then $t+1\le(b+1)(L+1)^d$, with $L=\log_2 n$ and $t$ the original circuit's depth. This gives the required bound for every $n$, with constant $b+1$.

**Key facts.** `BoolCircuit.TreeCircuit.toDAG_depth_le`, `BoolCircuit.polylog_add_one`.

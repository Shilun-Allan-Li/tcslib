<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: BoolCircuit.TreeCircuitFamily.isPolySize_toDAG -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial size under DAG conversion

**Claim.** If a tree-circuit family has size at most $a(n+1)^k$ at every input length $n$, then its associated DAG circuit family has polynomial size.

**Proof.** Choose $a$ and $k$ witnessing the assumed size bound. At each input length $n$, the tree-to-DAG size estimate bounds the converted circuit's size by $n$ plus the original size. The natural-number estimate that $s\le a(n+1)^k$ implies $n+s\le(a+1)(n+1)^{k+1}$ then supplies a polynomial bound for every $n$. Hence the converted family has polynomial size, witnessed by constants $a+1$ and $k+1$.

**Key facts.** `BoolCircuit.TreeCircuit.toDAG_size_le`, `BoolCircuit.poly_add_input`.

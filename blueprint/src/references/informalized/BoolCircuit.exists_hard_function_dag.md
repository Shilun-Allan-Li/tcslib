<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGHardFunctions.lean :: BoolCircuit.exists_hard_function_dag -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hard functions for small DAG circuits

**Claim.** For every $n>1$, some Boolean function on $n$ input bits disagrees with every well-formed fan-in-two acyclic circuit of size at most $2^n/(10n)$ on at least one input.

**Proof.** Set $S=2^n/(10n)$. The assumed bound on circuit size gives $10nS\le 2^n$ by the elementary floor-division inequality, and $n>1$ implies $1\le n$. The circuit-count estimate (`count_lt`) therefore bounds the number of functions computed by such circuits strictly below the total number $2^{2^n}$ of Boolean functions on $n$ bits. The counting argument that fewer than all functions are computed by these circuits (`exists_not_eval_dag_of_lt`) supplies a function outside that class. Being outside means precisely that each eligible circuit differs from it on some input.

**Key facts.** `BoolCircuit.count_lt`, `BoolCircuit.exists_not_eval_dag_of_lt`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: BoolCircuit.DAGCircuit.binarize_size_le_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Refined size bound for binarization

**Claim.** The size of the binarized circuit is at most $n+\sum_{g\in G}\max\{1,\ell(g)-1\}$, where $\ell(g)$ is the number of arguments of $g$.

**Proof.** The rewrite length estimate specialized to binarization (`rewriteGates_binarize_length_le`) says that the resulting gate list has length at most the sum, over original gates $g$, of $\max\{1,\ell(g)-1\}$. Its hypotheses hold because the circuit is acyclic, each negation has exactly one argument by well-formedness, and each gate's argument count is bounded by the circuit size (`DAGCircuit.args_length_le_size`). The circuit size is the number of input vertices plus the number of gates, so adding the $n$ inputs to this gate-count estimate yields the stated bound.

**Key facts.** `BoolCircuit.DAGCircuit.args_length_le_size`, `BoolCircuit.rewriteGates_binarize_length_le`.

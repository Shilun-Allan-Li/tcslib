<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.runWith_getD_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement on a Prefix of Gates

**Claim.** If $i\le |G|$ and $j<|v|+i$, the value at index $j$ after the first $i$ gates agrees with its value after all of $G$.

**Proof.** Split $G$ into its first $i$ gates and the remaining gates, using the list decomposition into `take` and `drop`. Evaluation of the concatenation first evaluates the prefix and then the suffix (`runWith_append`). The prefix output has length $|v|+i$, by `length_runWith` and the fact that $i\le |G|$. Therefore $j$ is an index in that intermediate output. The preservation-of-initial-values result (`runWith_getD_of_lt`), applied to evaluation of the suffix from this intermediate list, shows that this index is unchanged by the suffix. Hence the prefix and full evaluations agree at $j$.

**Key facts.** `BoolCircuit.runWith_append`, `BoolCircuit.length_runWith`, `BoolCircuit.runWith_getD_of_lt`.

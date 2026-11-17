<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/ShannonProbabilistic.lean :: BoolCircuit.prob_computableDAG_shannon_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shannon Bound for Small Circuits

**Claim.** For every $n$, the probability that a uniformly chosen Boolean function on $n$ inputs is computable by a circuit of size at most $\lfloor 2^n/(10n)\rfloor$ is at most $2^{-2^n/10}$.

**Proof.** Let $A$ be the set of functions computable with the stated size bound. The probability bound for small circuits (BoolCircuit.prob_computableDAG_le) gives an upper bound of $|A|\,2^{-2^n}$. Rewrite this product as the real number $|A|/2^{2^n}$, expressed as a nonnegative extended-real quantity. The Shannon fraction estimate (BoolCircuit.computableDAG_shannon_fraction_le) bounds that ratio by $2^{-2^n/10}$. Monotonicity of the embedding of nonnegative real numbers into extended nonnegative reals then yields the result.

**Key facts.** `BoolCircuit.prob_computableDAG_le`, `BoolCircuit.computableDAG_shannon_fraction_le`.

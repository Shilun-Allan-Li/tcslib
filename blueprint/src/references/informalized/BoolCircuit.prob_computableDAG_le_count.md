<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/ShannonProbabilistic.lean :: BoolCircuit.prob_computableDAG_le_count -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting Bound for Small Circuits

**Claim.** The probability that a uniformly chosen Boolean function on $n$ inputs is computable by a circuit of size at most $S$ is at most $(S+1)(3(S+1)^2)^S S\,2^{-2^n}$.

**Proof.** Apply the probability bound for small circuits (BoolCircuit.prob_computableDAG_le), which bounds the probability by the number of computable functions times $2^{-2^n}$. The circuit counting estimate (BoolCircuit.card_computable_dag_le) bounds that number by $(S+1)(3(S+1)^2)^S S$. Multiplying this cardinality bound by the nonnegative factor $2^{-2^n}$ gives the stated inequality.

**Key facts.** `BoolCircuit.prob_computableDAG_le`, `BoolCircuit.card_computable_dag_le`.

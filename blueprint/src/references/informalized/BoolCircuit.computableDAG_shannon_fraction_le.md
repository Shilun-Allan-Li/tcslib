<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/ShannonProbabilistic.lean :: BoolCircuit.computableDAG_shannon_fraction_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shannon Fraction Bound

**Claim.** For every number of input bits $n$, the fraction of Boolean functions computed by fan-in-two circuits of size at most $2^n/(10n)$ is at most $2^{-2^n/10}$.

**Proof.** Set $S=2^n/(10n)$ using natural division. The division bound gives $10nS\le 2^n$. If $S=0$, the number of computable functions is zero by the circuit-counting estimate (`BoolCircuit.card_computable_dag_le`), so the desired bound follows from positivity of the right-hand side. Otherwise $n\ge1$, and the counting estimate under the size hypotheses gives both an upper bound $2^{n(2(S+1))}$ for the number of computable functions and the numerical inequality $20n(S+1)\le 9\,2^n$ (`BoolCircuit.count_le_pow`). Regard the counting bound as a real inequality and divide by the positive number $2^{2^n}$. The numerical inequality implies $n(2(S+1))\le -2^n/10+2^n$, so monotonicity of the real exponential with base $2$ bounds the resulting numerator by $2^{-2^n/10}2^{2^n}$. Dividing by $2^{2^n}$ yields the stated fraction bound.

**Key facts.** `BoolCircuit.card_computable_dag_le`, `BoolCircuit.count_le_pow`.

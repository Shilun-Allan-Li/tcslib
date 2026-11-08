<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Uniform.lean :: BoolCircuit.DAGCircuitFamily.IsPUniform.isPolySize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial size from polynomial-time uniformity

**Claim.** If a circuit family is polynomial-time-uniform, then there are natural numbers $a$ and $k$ such that $\mathrm{size}(C_n)\leq a(n+1)^k$ for every $n$.

**Proof.** Choose a polynomial-time-uniformity function $f$ and its polynomial-time computation bound. A polynomial-time-computable function has polynomially bounded output length: there are constants $A,c$ such that $|f(x)|\leq A(|x|+1)^c$ for every input $x$ (Complexity.PolyTimeComputable.output_length_le). Apply this bound to the unary string of length $n$; its length is $n$, so the encoding of $C_n$ has length at most $A(n+1)^c$. The size of a circuit is at most the length of its encoding (BoolCircuit.DAGCircuit.size_le_length_encode). Combining the inequalities gives $\mathrm{size}(C_n)\leq A(n+1)^c$ for every $n$, as required.

**Key facts.** `Complexity.PolyTimeComputable.output_length_le`, `BoolCircuit.DAGCircuit.size_le_length_encode`.

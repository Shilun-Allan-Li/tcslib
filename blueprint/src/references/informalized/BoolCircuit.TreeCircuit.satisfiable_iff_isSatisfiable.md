<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSat.lean :: BoolCircuit.TreeCircuit.satisfiable_iff_isSatisfiable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Satisfiability and CNF Encoding

**Claim.** A Boolean circuit has an input assignment making it evaluate to true exactly when its CNF encoding, with the output required to be true, is satisfiable.

**Proof.** Suppose first that an input assignment $u$ makes the circuit $C$ evaluate to true. Extend $u$ to an assignment of the input and gate variables using the Tseitin assignment. The Tseitin clauses for $C$ and its subcircuits are then all satisfied (the fact that this assignment satisfies the encoding of any circuit is `tseitin_satisfied`). The additional first clause of $C$'s CNF requires the positive gate variable for $C$, which is true because $C$ evaluates to true. Thus the whole encoding is satisfied.

Conversely, suppose an assignment satisfies the CNF. Read its input variables as a Boolean input assignment $u$, choosing true exactly when the corresponding input variable is assigned true. Then $u(i)=\mathrm{true}$ exactly when the encoding assignment makes input variable $i$ true. The first clause of the CNF forces the gate variable for $C$ to be true. Since the assignment satisfies all Tseitin clauses of $C$, the evaluation equivalence for a Tseitin-satisfied encoding (`eval_iff_of_tseitin_satisfied`) says that $C$ evaluates to true under $u$.

**Key facts.** `BoolCircuit.tseitin_satisfied`, `BoolCircuit.eval_iff_of_tseitin_satisfied`.

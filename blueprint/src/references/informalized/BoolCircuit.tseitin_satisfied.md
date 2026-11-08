<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSat.lean :: BoolCircuit.tseitin_satisfied -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfaction of the Tseitin Encoding

**Claim.** For an input assignment $u$, assigning each input variable its value under $u$ and each gate variable the value obtained by evaluating the circuit at that gate satisfies every clause in the Tseitin encoding of the circuit.

**Proof.** Use structural induction on the circuit. For a literal $l$, its gate variable is true exactly when $l$ evaluates to true, by the definition of the assignment and the evaluation of a literal gate (\texttt{BoolCircuit.TreeCircuit.eval\_lit}). The input literals encode the value of $l$ and its negation: the positive encoding is true exactly when $l$ evaluates to true, and the negated encoding exactly when it does not (\texttt{BoolCircuit.evalLiteral\_toCktLiteral\_iff} and \texttt{BoolCircuit.evalLiteral\_toCktLiteralNeg\_iff}). Thus, whichever value $l$ has, each of the two clauses in its encoding has a satisfied literal. For a node, a clause in its Tseitin formula either belongs to the gate clauses or to the Tseitin formula of one of its children. The gate clauses are satisfied by the gate and child evaluation values (\texttt{BoolCircuit.gateClauses\_satisfied}); clauses from a child are satisfied by the induction hypothesis. Therefore every clause is satisfied.

**Key facts.** `BoolCircuit.TreeCircuit.ind`, `BoolCircuit.TreeCircuit.eval_lit`, `BoolCircuit.evalLiteral_toCktLiteral_iff`, `BoolCircuit.evalLiteral_toCktLiteralNeg_iff`, `BoolCircuit.gateClauses_satisfied`.

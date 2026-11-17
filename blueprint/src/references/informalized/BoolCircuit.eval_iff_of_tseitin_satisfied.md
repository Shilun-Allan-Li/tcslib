<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSat.lean :: BoolCircuit.eval_iff_of_tseitin_satisfied -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Evaluation from Tseitin Clauses

**Claim.** If all clauses in a tree circuit's Tseitin formula are satisfied by \alpha, then the circuit evaluates to true under $u$ exactly when \alpha makes its gate variable true.

**Proof.** Proceed by induction on the circuit. For a literal circuit, satisfaction of the first Tseitin clause says that either its gate variable is true or the encoded literal is true; satisfaction of the second says that either the gate variable is false or the complementary encoded literal is true. Literal evaluation agrees with the encoded literal (BoolCircuit.evalLiteral_toCktLiteral_iff), while the complementary encoding agrees with failure of the original literal (BoolCircuit.evalLiteral_toCktLiteralNeg_iff). Together these two clause conditions give precisely the desired equivalence between the literal's value and its gate variable. The evaluation of a literal circuit is its literal's evaluation (BoolCircuit.TreeCircuit.eval_lit). For a gate with children, the induction hypotheses give this equivalence for every child, and the satisfied clauses belonging to the gate then imply the equivalence for the gate itself (BoolCircuit.eval_node_iff_of_gateClauses). The clauses for each child are among the full Tseitin formula, so the induction hypotheses apply.

**Key facts.** `BoolCircuit.TreeCircuit.ind`, `BoolCircuit.evalLiteral_toCktLiteral_iff`, `BoolCircuit.evalLiteral_toCktLiteralNeg_iff`, `BoolCircuit.TreeCircuit.eval_lit`, `BoolCircuit.eval_node_iff_of_gateClauses`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSat.lean :: BoolCircuit.evalLiteral_toCktLiteralNeg_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Negated Circuit Literal

**Claim.** Under the stated correspondence between the Boolean input assignment $u$ and the truth assignment $\alpha$, the negated circuit literal associated with any literal $l$ is true under $\alpha$ exactly when $l$ evaluates to false under $u$.

**Proof.** There are two cases, according to the sign of $l$, and in each case two cases for the Boolean value $u(l.idx)$. If the sign is positive, the associated circuit literal is the negation of the corresponding input variable; by the assignment hypothesis, it is true exactly when that input bit is false, which is exactly when the positive literal evaluates to false. If the sign is negative, the associated circuit literal is the positive input variable; it is true exactly when the input bit is true, which is exactly when the negative literal evaluates to false. These cases establish the equivalence.

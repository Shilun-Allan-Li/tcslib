<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.eval_toMvPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial representation of circuit evaluation

**Claim.** For an algebraic circuit $C$ and an integer input assignment $x$, evaluating the multivariable polynomial associated with $C$ at $x$ gives $C$’s evaluation at $x$.

**Proof.** The polynomial associated with $C$ is defined by evaluating the circuit at the tuple of polynomial variables. The theorem `aeval_toMvPolynomial` identifies its evaluation under the algebra homomorphism determined by $x$ with the circuit’s evaluation at $x$. For integer coefficients, evaluation by that algebra homomorphism agrees with ordinary multivariable polynomial evaluation (`aeval_eq_eval`). Combining these equalities gives the result.

**Key facts.** `Randomized.AlgCircuit.aeval_toMvPolynomial`.

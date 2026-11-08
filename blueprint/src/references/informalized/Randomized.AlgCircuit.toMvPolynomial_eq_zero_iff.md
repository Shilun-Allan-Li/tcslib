<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.toMvPolynomial_eq_zero_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial vanishing criterion

**Claim.** For any arithmetic circuit $C$ on $n$ inputs, its integer-coefficient multivariate polynomial is zero if and only if its evaluation is zero at every integer assignment to the inputs.

**Proof.** A multivariate polynomial is zero exactly when its evaluations at all assignments of its variables are zero, by the function-extensionality criterion for multivariate polynomials. For each integer assignment, evaluating the polynomial represented by $C$ gives exactly the circuit's evaluation (`Randomized.AlgCircuit.eval_toMvPolynomial`). Applying this evaluation identity pointwise yields the stated equivalence.

**Key facts.** `Randomized.AlgCircuit.eval_toMvPolynomial`.

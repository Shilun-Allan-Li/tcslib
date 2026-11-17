<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.aeval_toMvPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit polynomial evaluation

**Claim.** Evaluating the integer-coefficient polynomial represented by a circuit at $x$ gives the same value as evaluating the circuit directly at $x$.

**Proof.** The circuit evaluation commutes with ring homomorphisms: applying a homomorphism to the circuit’s value at a tuple is the same as evaluating the circuit after applying the homomorphism coordinatewise (`Randomized.AlgCircuit.map_eval`). Take the homomorphism that evaluates integer-coefficient polynomials at $x$. The polynomial representation is the circuit evaluation at the formal variables, and this homomorphism sends each formal variable to the corresponding coordinate of $x$. Thus the resulting value is the circuit evaluated at $x$.

**Key facts.** `Randomized.AlgCircuit.map_eval`.

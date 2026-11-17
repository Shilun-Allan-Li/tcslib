<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.toMvPolynomial_subCircuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial of a subcircuit construction

**Claim.** For circuits $C$ and $C'$ with nonempty gate lists, the polynomial of the specified shifted-node subtraction circuit is the polynomial of $C$ minus the polynomial of $C'$.

**Proof.** The evaluation of the constructed subtraction circuit at any input assignment is the difference of the evaluations of $C$ and $C'$ (`Randomized.AlgCircuit.eval_subCircuit`). Evaluate at the formal variables over the integers; by the definition of the polynomial represented by a circuit, these three evaluations are their respective represented polynomials. The claimed identity follows.

**Key facts.** `Randomized.AlgCircuit.eval_subCircuit`.

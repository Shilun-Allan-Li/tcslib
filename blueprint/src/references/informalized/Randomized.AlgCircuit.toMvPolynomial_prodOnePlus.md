<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuitExample.lean :: Randomized.AlgCircuit.toMvPolynomial_prodOnePlus -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial of the product circuit

**Claim.** For every natural number $n$, the integer-coefficient multivariate polynomial represented by the circuit for the product of the first $n$ factors is $\prod_{i\in\mathrm{Fin}(n)}(1+X_i)$.

**Proof.** Run the product-circuit gate list on the formal variables. Its established run formula says the value at position $3n$ is the product over $i<n$ of one plus the value of `varOrOne i` (`Randomized.AlgCircuit.run_prodOnePlusGates`). The circuit size is $3n+1$ (`Randomized.AlgCircuit.size_prodOnePlus`), so its output position, size minus one, is exactly $3n$. Thus the represented polynomial is that range product. Reindex the range product by the finite type of indices below $n$; for each such index, `varOrOne` selects the corresponding input variable, so its gate value on the formal variables is $X_i$. This gives the claimed finite product.

**Key facts.** `Randomized.AlgCircuit.run_prodOnePlusGates`, `Randomized.AlgCircuit.size_prodOnePlus`.

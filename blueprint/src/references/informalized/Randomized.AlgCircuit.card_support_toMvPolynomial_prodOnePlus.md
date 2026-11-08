<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuitExample.lean :: Randomized.AlgCircuit.card_support_toMvPolynomial_prodOnePlus -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Support size of the product circuit

**Claim.** For every natural number $n$, the polynomial computed by the constructed arithmetic circuit for $\prod_{i=1}^{n}(1+X_i)$ has exactly $2^n$ monomials with nonzero coefficient.

**Proof.** The circuit computes the polynomial $\prod_{i : \mathrm{Fin}\ n}(1+X_i)$, by the circuit evaluation identity for this construction (`toMvPolynomial_prodOnePlus`). The support of that product has cardinality $2^n$ (`card_support_prod_one_add_X`). Substituting the first identity into the second gives the claimed support size.

**Key facts.** `Randomized.AlgCircuit.toMvPolynomial_prodOnePlus`, `Randomized.AlgCircuit.card_support_prod_one_add_X`.

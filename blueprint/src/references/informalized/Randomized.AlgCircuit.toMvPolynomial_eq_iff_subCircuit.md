<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.toMvPolynomial_eq_iff_subCircuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial equality and circuit difference

**Claim.** For circuits $C$ and $C'$ with nonempty gate lists, their represented integer-coefficient multivariate polynomials are equal if and only if the polynomial represented by their specified shifted-node subtraction circuit is zero.

**Proof.** The polynomial of the subtraction circuit is the difference of the two circuit polynomials (`Randomized.AlgCircuit.toMvPolynomial_subCircuit`). Substituting this identity reduces the claim to the ring fact that $P=Q$ if and only if $P-Q=0$.

**Key facts.** `Randomized.AlgCircuit.toMvPolynomial_subCircuit`.

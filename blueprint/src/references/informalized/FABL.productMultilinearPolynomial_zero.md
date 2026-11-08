<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ReasonableProductPolynomials.lean :: FABL.productMultilinearPolynomial_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Coefficients Give the Zero Polynomial

**Claim.** For every $n$ and every $x\in\mathbb R^n$, the product multilinear polynomial with all coefficients zero evaluates to zero at $x$.

**Proof.** Proceed by induction on $n$. When $n=0$, the polynomial is the coefficient of the empty set, which is zero. For the step from $n$ to $n+1$, split the polynomial into its first-coordinate term and its remaining term. Both resulting polynomials have all coefficients zero, so by the induction hypothesis both evaluate to zero; hence their sum, including the first-coordinate multiple, is zero.

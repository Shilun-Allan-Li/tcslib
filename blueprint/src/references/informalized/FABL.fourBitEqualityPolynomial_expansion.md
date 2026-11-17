<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdFunctions.lean :: FABL.fourBitEqualityPolynomial_expansion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Four-bit equality polynomial expansion

**Claim.** For every sign vector on four coordinates, the four-bit equality polynomial equals the multilinear polynomial with coefficient $-3$ on the empty set, coefficient $1$ on each two-element subset, and coefficient $0$ on every other subset.

**Proof.** In the multilinear sum, every subset outside the empty set and the six two-element subsets has coefficient zero. Therefore the sum reduces to those seven terms. The empty-set term contributes $-3$, and each of the six pair terms contributes its corresponding monomial with coefficient $1$. These are exactly the terms defining the four-bit equality polynomial, so the two expressions agree.

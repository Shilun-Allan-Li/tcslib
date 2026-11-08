<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.krawtchoukValue_eq_coeff_negativeCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Krawtchouk Coefficient Formula

**Claim.** For a sign vector, the sum of its degree-$j$ coordinate monomials is the coefficient of $X^j$ in $(1-X)^m(1+X)^{n-m}$, where $m$ is the number of negative coordinates.

**Proof.** Apply the coefficient identity for the Krawtchouk generating polynomial: its degree-$j$ coefficient equals the sum of degree-$j$ monomials. Then replace that generating polynomial by its factorization according to the number of negative coordinates. This gives the claimed coefficient formula.

**Key facts.** `FABL.coeff_krawtchoukGeneratingPolynomial`, `FABL.krawtchoukGeneratingPolynomial_eq_negativeCount`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.krawtchoukPolynomial_represents -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial representation of Krawtchouk values

**Claim.** The Krawtchouk polynomial has degree $j$, and its value at the number of negative coordinates of $x$ equals the Krawtchouk value of $x$.

**Proof.** The degree assertion is exactly the degree theorem for the Krawtchouk polynomial (`krawtchoukPolynomial_natDegree`). For the value assertion, put $z$ equal to the number of negative coordinates of $x$. This count is at most $n$ (`negativeCoordinateCount_le`), so the evaluation formula for the polynomial applies: its value at $z$ is the coefficient of $X^j$ in $(1-X)^z(1+X)^{n-z}$ (`eval_krawtchoukPolynomial_eq_coeff_countGenerating`). The Krawtchouk value of $x$ is the same coefficient (`krawtchoukValue_eq_coeff_negativeCount`). Hence the two values agree.

**Key facts.** `FABL.krawtchoukPolynomial_natDegree`, `FABL.negativeCoordinateCount_le`, `FABL.eval_krawtchoukPolynomial_eq_coeff_countGenerating`, `FABL.krawtchoukValue_eq_coeff_negativeCount`.

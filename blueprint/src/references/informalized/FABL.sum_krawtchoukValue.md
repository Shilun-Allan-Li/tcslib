<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.sum_krawtchoukValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum of Krawtchouk Values

**Claim.** Summing the Krawtchouk values of a sign vector over all degrees gives $2^n$ times its all-ones point indicator polynomial.

**Proof.** Insert the factor $1^j$ into each degree-$j$ term and apply the Krawtchouk generating identity (\texttt{FABL.sum_krawtchoukValue_mul_pow}) at parameter $1$. The resulting sum is over all subsets, with each subset contributing its monomial at the sign vector. The sum of all these monomials equals $2^n$ times the all-ones point indicator polynomial (\texttt{FABL.sum_monomial_eq_point_indicator}), proving the formula.

**Key facts.** `FABL.sum_krawtchoukValue_mul_pow`, `FABL.sum_monomial_eq_point_indicator`.

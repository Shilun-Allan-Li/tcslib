<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.sum_krawtchoukSummand_leadingCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leading Coefficient Sum

**Claim.** The sum of the leading coefficients of the indicated Krawtchouk summand polynomials, over $k=0,\ldots,j$, is $(-1)^j2^j/j!$.

**Proof.** For each $k$ in the range, the leading coefficient formula for a Krawtchouk summand (\texttt{FABL.krawtchoukSummand_leadingCoeff}) and the signed factorial identity (\texttt{FABL.signed_factorial_inverse_identity}) rewrite that coefficient as $(-1)^j\binom{j}{k}/j!$. Factoring out $(-1)^j/j!$ leaves the sum of the binomial coefficients $\binom{j}{k}$ for $k=0,\ldots,j$. By the binomial theorem this sum is $2^j$, giving the stated value.

**Key facts.** `FABL.krawtchoukSummand_leadingCoeff`, `FABL.signed_factorial_inverse_identity`.

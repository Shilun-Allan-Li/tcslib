<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.sum_monomial_eq_point_indicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum of sign monomials

**Claim.** For every sign vector $x\in\{-1,1\}^n$, the sum of its monomials over all subsets of coordinates equals $2^n$ times the indicator polynomial at the all-positive vector.

**Proof.** Evaluate the generating polynomial for the monomials at $1$. Its evaluation formula (\(\texttt{FABL.eval_krawtchoukGeneratingPolynomial}\)) says this is the sum of all monomials, since $1^{|S|}=1$. The product formula for that polynomial then gives $\prod_{i=1}^n(1+x_i)$, where the sign value of the all-positive vector is $1$ (\(\texttt{FABL.signValue_one}\)). Finally, factor $2$ from each coordinate: the product becomes $2^n\prod_i(1+x_i)/2$, which is precisely $2^n$ times the stated indicator polynomial.

**Key facts.** `FABL.eval_krawtchoukGeneratingPolynomial`, `FABL.signValue_one`.

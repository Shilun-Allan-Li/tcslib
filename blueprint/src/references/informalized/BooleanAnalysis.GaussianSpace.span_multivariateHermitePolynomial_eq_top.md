<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Span.lean :: BooleanAnalysis.GaussianSpace.span_multivariateHermitePolynomial_eq_top -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hermite Polynomial Spanning

**Claim.** For every nonnegative integer $n$, the normalized multivariate Hermite polynomials indexed by multi-indices in $\mathbb N^n$ span the real vector space of polynomials in $n$ variables.

**Proof.** It suffices to show that every polynomial belongs to the span. Use the additive induction principle for multivariate polynomials: each polynomial is a sum of scalar multiples of monomials, so it is enough to handle a monomial with exponent multi-index $u$ and coefficient $a$. The coordinate polynomial product spanning lemma says that for any choice of one-variable polynomials, their product after placing each in its corresponding coordinate lies in the span of the multivariate Hermite polynomials (`coordinatePolynomialProduct_mem_span_hermite`). Choose the polynomial in coordinate $i$ to be $X^{u_i$. The resulting coordinate product is precisely the monomial with exponent $u$, so multiplying it by $a$ keeps it in the span. Additivity then gives the result for every polynomial.

**Key facts.** `BooleanAnalysis.GaussianSpace.coordinatePolynomialProduct_mem_span_hermite`.

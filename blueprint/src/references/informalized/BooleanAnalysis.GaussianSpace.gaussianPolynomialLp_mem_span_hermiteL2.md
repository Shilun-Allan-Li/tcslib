<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basis.lean :: BooleanAnalysis.GaussianSpace.gaussianPolynomialLp_mem_span_hermiteL2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Polynomials Lie in the Hermite Span

**Claim.** For every $n$ and every real polynomial $P$ in $n$ variables, its Gaussian $L^2$ class belongs to the real linear span of the multivariate Hermite functions.

**Proof.** Consider the subspace of polynomials spanned by the multivariate Hermite polynomials. The proof first shows that this entire subspace maps into the span of the Hermite functions: each generating Hermite polynomial maps to its corresponding Hermite function, by the identification of their Gaussian $L^2$ classes (`gaussianPolynomialLp_hermite`), and the image of a subspace under a linear map respects this containment. The multivariate Hermite polynomials span the whole polynomial space (`span_multivariateHermitePolynomial_eq_top`). Hence $P$ lies in that polynomial span, and its image under the Gaussian polynomial map lies in the Hermite-function span, as required.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianPolynomialLp_hermite`, `BooleanAnalysis.GaussianSpace.span_multivariateHermitePolynomial_eq_top`.

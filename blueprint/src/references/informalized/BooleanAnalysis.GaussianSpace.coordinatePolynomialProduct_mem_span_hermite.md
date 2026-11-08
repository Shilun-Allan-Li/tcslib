<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Span.lean :: BooleanAnalysis.GaussianSpace.coordinatePolynomialProduct_mem_span_hermite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Polynomial Products Lie in the Hermite Span

**Claim.** For each coordinate polynomial $p_i$, the product of the polynomials $p_i$ evaluated in their respective coordinates lies in the real linear span of the multivariate Hermite polynomials.

**Proof.** Let $N$ be the span of the multivariate Hermite polynomials, and consider the multilinear map that sends a tuple of one-variable polynomials to the product of their coordinate evaluations. Compose this map with the quotient map by $N$. To show the composite is zero, it suffices to check it on tuples from a basis of the one-variable polynomial space, since multilinear maps agreeing on basis tuples agree everywhere. On such a basis tuple, the coordinate product is exactly a multivariate Hermite polynomial: the basis elements identify with the normalized Hermite polynomials ($\texttt{normalizedHermiteBasis\_apply}$). Each such polynomial belongs to $N$ by the definition of span, so its quotient class is zero. The composite therefore vanishes on every tuple, including $(p_i)_i$. This says precisely that their coordinate product belongs to $N$.

**Key facts.** `BooleanAnalysis.GaussianSpace.normalizedHermiteBasis_apply`.

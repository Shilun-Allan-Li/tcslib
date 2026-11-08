<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/polylogIndep.lean :: KWise_Fools_Polynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# K-wise independence and low-degree polynomials

**Claim.** If $\mu$ is uniform on every joint distribution of at most $k$ coordinates, then every multilinear polynomial of degree at most $k$ has the same expectation under $\mu$ as under the uniform distribution on the Boolean cube.

**Proof.** Write the polynomial as a sum of monomials, with coefficient $c_S$ on the monomial indexed by $S$. Since its degree is at most $k$, the coefficients vanish whenever $|S|>k$. By linearity of expectation, its expectation under either distribution is the sum of the coefficient-weighted expectations of its monomials. For every term with $|S|\le k$, the monomial expectations agree by the fact that $k$-wise independence fools a monomial (KWise_Fools_Monomial). Terms with $|S|>k$ contribute zero because their coefficients vanish. The two polynomial expectations are therefore equal.

**Key facts.** `KWise_Fools_Monomial`.

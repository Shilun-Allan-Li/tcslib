<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Orthogonality.lean :: BooleanAnalysis.GaussianSpace.iterate_derivative_hermite_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Top derivative of a Hermite polynomial

**Claim.** For every nonnegative integer $k$, differentiating the degree-$k$ Hermite polynomial $k$ times gives the constant polynomial with value $k!$.

**Proof.** Compare coefficients of both polynomials. The coefficient formula for an iterated derivative expresses the coefficient of degree $m$ as the original coefficient of degree $m+k$, multiplied by the corresponding descending factorial. When $m=0$, the leading coefficient of the degree-$k$ Hermite polynomial is one, and the descending factorial is $k!$, so the constant coefficient is $k!$. When $m>0$, the coefficient of degree $m+k$ in the Hermite polynomial is zero because its degree is $k<m+k$; hence every positive-degree coefficient vanishes. These coefficient identities establish equality of the polynomials.

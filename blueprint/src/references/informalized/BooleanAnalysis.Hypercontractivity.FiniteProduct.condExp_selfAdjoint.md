<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Basic.lean :: BooleanAnalysis.Hypercontractivity.FiniteProduct.condExp_selfAdjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Self-Adjointness of Conditional Expectation

**Claim.** For any two real-valued functions on the product outcome space, taking conditional expectation onto the coordinates in $S$ is self-adjoint with respect to product expectation: $\mathbb E_P[fE_Sg]=\mathbb E_P[(E_Sf)g]$.

**Proof.** Expand the conditional expectation in the left-hand side as an inner expectation over an independent sample $y$. This writes the expression as the iterated expectation of $f(x)g(z)$, where $z$ uses the coordinates of $x$ on $S$ and those of $y$ off $S$. Apply the exchange-of-product-samples identity (`expect_swap_samples`): swapping the two samples on the two coordinate blocks preserves their joint product distribution. After this swap, the integrand can be written as $f(z)g(x)$, with $z$ now using $x$ on $S$ and $y$ off $S$. Regrouping the inner expectation gives $(E_Sf)(x)g(x)$, which is the right-hand side.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_swap_samples`.

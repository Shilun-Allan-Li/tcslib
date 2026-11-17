<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolFourier.lean :: BoolFourier.expectation_factorizes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factorization of Product Expectations

**Claim.** For coordinate functions $g_i$ on the Boolean cube, the uniform expectation of their pointwise product factors as the product of their individual two-point averages: $\mathbb E_x[\prod_i g_i(x_i)]=\prod_i (g_i(0)+g_i(1))/2$.

**Proof.** After writing the expectation as a sum over all Boolean vectors and distributing the product over the coordinatewise sums, the right-hand side becomes a sum indexed by subsets of coordinates. Associate to each vector $x$ the subset of coordinates where $x_i$ is false. This is a bijection: a subset determines the unique vector that is false on it and true off it. Under this correspondence, the product contribution is the product of $g_i(0)$ over the subset and of $g_i(1)$ over its complement. Thus the subset-indexed sum is exactly the sum of $\prod_i g_i(x_i)$ over all Boolean vectors, with the common normalization by $2^n$.

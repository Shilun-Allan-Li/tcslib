<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications.lean :: BooleanAnalysis.Hypercontractivity.product_stability_sq_eq_norm_noise_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stability as a squared noisy norm

**Claim.** For any finite product probability space, real-valued function $f$, and real $c$, the stability of $f$ at rate $c^2$ equals the square of the second norm of its noise at rate $c$.

**Proof.** First show that product noise is self-adjoint for the expectation pairing. Expand noise and each component into its finite sums; move constant coefficients outside expectations, then use self-adjointness of conditional expectation to exchange the two functions. Next, the component-noise identity shows that applying noise twice at rate $c$ multiplies each component by $c^{2|S|}$, so the result is noise at rate $c^2$. Therefore stability at rate $c^2$ can be rewritten as the expectation of the square of the noise of $f$ at rate $c$. This expectation is nonnegative, since it is a sum of squared values weighted by nonnegative masses. By the definition of the second norm, its square is precisely that expectation.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_sum`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const_mul`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.condExp_selfAdjoint`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.component_noise`.

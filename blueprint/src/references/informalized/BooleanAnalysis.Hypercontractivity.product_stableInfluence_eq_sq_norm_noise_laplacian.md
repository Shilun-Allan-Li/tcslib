<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications.lean :: BooleanAnalysis.Hypercontractivity.product_stableInfluence_eq_sq_norm_noise_laplacian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stable influence as a noisy Laplacian norm

**Claim.** For any finite product probability space, rate $\rho\ge0$, function $f$, and coordinate $i$, $\rho$ times the stable influence of $f$ at $i$ equals the square of the second norm of the noise at rate $\sqrt{\rho}$ applied to the coordinate Laplacian of $f$.

**Proof.** The second norm squared is the expectation of the square of the noisy Laplacian. Parseval's identity expresses this expectation as the sum of the expected squared components. Noise multiplies the component at $S$ by $(\sqrt{\rho})^{|S|}$, and the Laplacian keeps that component exactly when $i\in S$, annihilating it otherwise. Thus only sets containing $i$ contribute. For such a set, the coefficient on its squared component is $(\sqrt{\rho})^{2|S|}=\rho^{|S|}=\rho\,\rho^{|S|-1}$. Since $i\in S$ implies $|S|\ge1$, this is precisely the coefficient in $\rho$ times the stable-influence sum. The remaining terms vanish, proving the identity.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.parseval`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.component_noise`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.component_laplacian`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const_mul`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const`.

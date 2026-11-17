<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/General.lean :: BooleanAnalysis.Hypercontractivity.product_noise_inverse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inverse product noise

**Claim.** For any finite product probability space, nonzero real rate $\rho$, and real-valued function $f$, applying product noise at rate $\rho^{-1}$ and then at rate $\rho$ recovers $f$.

**Proof.** Evaluate both sides at an outcome and expand the outer noise as a sum over coordinate sets. The component of the inner noisy function at a set $S$ is $\rho^{-\lvert S\rvert}$ times the corresponding component of $f$ (the component-noise identity). Multiplying by the outer coefficient $\rho^{\lvert S\rvert}$ cancels this factor because $\rho\ne0$. The resulting sum is the sum of all components of $f$. By the signed powerset-sum identity, this equals the conditional expectation with every coordinate fixed. That conditional expectation is the constant expectation of the value $f(x)$, hence equals $f(x)$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.RandomizationAux.component_noise`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.sum_powerset_signed_sum`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const`.

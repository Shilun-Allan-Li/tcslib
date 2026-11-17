<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications/LowDegree.lean :: BooleanAnalysis.Hypercontractivity.product_noise_norm_two_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise contraction in the second norm

**Claim.** For a finite product probability space, any $0\le c\le1$, and every real-valued function $f$, product noise contracts the second norm: $\|T_c f\|_{2,P}\le\|f\|_{2,P}$.

**Proof.** By Parseval's identity, the square of the second norm of a function is the sum, over coordinate sets $S$, of the expected squares of its components. Noise multiplies the component at $S$ by $c^{|S|}$, so its contribution to that sum is multiplied by $c^{2|S|}$. Since $0\le c\le1$, this factor is at most one. Each expected square of a component is nonnegative because the product-space masses are nonnegative. Thus every term in the Parseval sum for the noisy function is at most the corresponding term for $f$. Taking square roots gives the asserted norm inequality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.parseval`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.component_noise`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const_mul`.

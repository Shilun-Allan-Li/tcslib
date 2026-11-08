<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/NoiseKernel.lean :: BooleanAnalysis.Hypercontractivity.FiniteProduct.noise_norm_one_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Moment Noise Contraction

**Claim.** For a product of finite probability spaces with strictly positive coordinate weights, the first moment norm of the noisy function is at most that of the original function whenever $0\le\rho\le1$.

**Proof.** For each pair of product points $x,y$, define the transition weight $K(x,y)=\prod_i\bigl(\rho\mathbf 1_{x_i=y_i}+(1-\rho)w_i(y_i)\bigr)$. Each factor is nonnegative, so $K(x,y)\ge0$. The noise operator has the kernel representation $T_\rho f(x)=\sum_y K(x,y)f(y)$ (`noise_kernel`). The triangle inequality for finite sums therefore gives $|T_\rho f(x)|\le\sum_yK(x,y)|f(y)|$. Next, for each fixed $y$, summing the incoming mass yields $\sum_x P(x)K(x,y)=P(y)$. Indeed, the product sum factors coordinatewise, and each coordinate factor is $\rho w_i(y_i)+(1-\rho)w_i(y_i)\sum_a w_i(a)=w_i(y_i)$, using that the coordinate weights sum to one. Multiply the pointwise bound by $P(x)$ and sum over $x$. Interchanging the finite sums and applying this stationarity identity gives $\sum_yP(y)|f(y)|$, which is exactly the desired first moment bound.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.noise_kernel`.

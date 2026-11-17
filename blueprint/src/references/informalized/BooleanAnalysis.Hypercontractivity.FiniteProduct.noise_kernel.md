<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/NoiseKernel.lean :: BooleanAnalysis.Hypercontractivity.FiniteProduct.noise_kernel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Noise Kernel Formula

**Claim.** The product noise operator has the stated kernel: its value at $x$ is the sum over outcomes $y$ of the product of the coordinate kernels $\rho\mathbf{1}_{x_i=y_i}+(1-\rho)w_i(y_i)$, multiplied by $f(y)$.

**Proof.** First replace each component of the noise operator by its kernel expansion (`component_kernel`). Distribute the sum over subsets through the finite sums, interchange the subset and outcome sums, and collect the coefficient of each $f(y)$. For fixed $y$, the coefficient is a sum over subsets $S$ of products whose coordinate factor is the difference $\mathbf{1}_{x_i=y_i}-w_i(y_i)$ on $S$ and $w_i(y_i)$ off $S$, with the corresponding powers of $\rho$. Expanding a product of coordinate sums shows this subset sum equals $\prod_i\bigl(\rho(\mathbf{1}_{x_i=y_i}-w_i(y_i))+w_i(y_i)\bigr)$. Simplifying each factor gives $\rho\mathbf{1}_{x_i=y_i}+(1-\rho)w_i(y_i)$, proving the formula.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.component_kernel`.

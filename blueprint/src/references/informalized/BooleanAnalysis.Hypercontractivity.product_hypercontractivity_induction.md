<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/General.lean :: BooleanAnalysis.Hypercontractivity.product_hypercontractivity_induction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Hypercontractivity by Tensorization

**Claim.** Assuming the stated one-coordinate norm inequality, the product noise operator satisfies $\|T_\rho f\|_{q,P}\le\|f\|_{p,P}$ whenever $1\le p\le q$ and $0\le\rho\le1$.

**Proof.** Since $1\le p\le q$, either $q>1$ or $p=q=1$. In the first case, express the product noise operator using its product kernel (`noise_kernel`). Each kernel factor is nonnegative: it is the sum of $\rho$ times an equality indicator and $1-\rho$ times a coordinate weight, with both coefficients nonnegative. The one-coordinate hypothesis is exactly the coordinate norm bound for this kernel. The finite tensorization theorem `FiniteTensorization.norm_tensorization` therefore yields the claimed product norm inequality.

In the remaining case $p=q=1$, the result is the contraction of the first-moment norm under noise, given by `FiniteProduct.noise_norm_one_le`.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.noise_kernel`, `BooleanAnalysis.Hypercontractivity.FiniteTensorization.norm_tensorization`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.noise_norm_one_le`.

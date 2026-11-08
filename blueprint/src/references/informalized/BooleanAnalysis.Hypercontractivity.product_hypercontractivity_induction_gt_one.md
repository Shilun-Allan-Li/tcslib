<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/General.lean :: BooleanAnalysis.Hypercontractivity.product_hypercontractivity_induction_gt_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tensorization Above the First Moment

**Claim.** Under the stated coordinate-wise norm bound, if $1\le p$ and $1<q$, then every function on the product space satisfies $\|T_\rho f\|_{q,P}\le\|f\|_{p,P}$.

**Proof.** Unfold the product expectation and norm, and write the noise operator through its product kernel (`noise_kernel`). Each coordinate kernel is nonnegative because it is a sum of nonnegative terms: $\rho$ times an equality indicator and $(1-\rho)$ times a coordinate weight. The assumed one-coordinate inequality gives the required $q$-norm bound for each coordinate kernel. Applying the finite tensorization theorem `FiniteTensorization.norm_tensorization` to these kernels and the product weights gives the desired inequality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.noise_kernel`, `BooleanAnalysis.Hypercontractivity.FiniteTensorization.norm_tensorization`.

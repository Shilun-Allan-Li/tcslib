<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/ThirdMoments.lean :: BooleanAnalysis.GaussianSpace.Invariance.affine_product_three_norm_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-norm bound for a product measure

**Claim.** Under the assumed affine three-norm bound for $\nu$, the three-norm squared of $(u,v,w)\mapsto u+vw$ under $\tau\times\nu$ is bounded by the sum of the three-norm squares of the first coordinate and the scaled second coordinate under $\tau$.

**Proof.** For each $z=(u,v)$, set $A(z)=|u|^2$ and $B(z)=|v/\rho|^2$. The assumed affine estimate, raised to the power $3/2$, bounds the integral over $w$ of $|u+vw|^3$ by $(A(z)+B(z))^{3/2}$. Integrating this section bound over $z$ and using the product integral formula bounds the product-space three-norm squared by $\bigl(\int (A+B)^{3/2}\,d\tau\bigr)^{2/3}$. The $L^{3/2}$ triangle inequality bounds this last quantity by $\|A\|_{3/2}+\|B\|_{3/2}$. Since $A=|u|^2$ and $B=|v/\rho|^2$, these two terms are precisely the respective three-norms squared asserted in the result. The argument uses extended nonnegative integrals, so the inequalities also cover infinite values.

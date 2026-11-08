<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Bounds.lean :: BooleanAnalysis.Hypercontractivity.low_norms_hypercontractivity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Intermediate norm hypercontractivity

**Claim.** For $1<p\le u\le2$, the noise operator with parameter $\sqrt{(p-1)/(u-1)}$ maps the $p$-norm to at most the $u$-norm: $\|T_{\sqrt{(p-1)/(u-1)}}f\|_u\le\|f\|_p$.

**Proof.** Let $\rho=\sqrt{(p-1)/(u-1)}$. The hypotheses imply $1<p\le u$, so $u>1$, and $0\le\rho\le1$. If $p=u$, then $\rho=1$ and the claim is equality. If $u=2$, it is the previously established $(p,2)$ hypercontractive bound. In the remaining case $p<u<2$, the one-bit theorem supplies the one-coordinate norm inequality. Hölder's inequality turns this into a two-function inner-product bound in dimension one, with conjugate exponent $u/(u-1)$ on the first function. The hypercontractivity induction theorem extends that bilinear bound to the whole cube. Finally, Hölder duality represents the $u$-norm of $T_\rho f$ as bounded above by its pairing with a function of conjugate norm at most one. Applying the extended bilinear estimate to that function and $f$ gives the desired bound.

**Key facts.** `BooleanAnalysis.Hypercontractivity.Interpolation.sqrt_div_le_one`, `BooleanAnalysis.Hypercontractivity.trivial_contractivity`, `BooleanAnalysis.Hypercontractivity.bridging_hypercontractivity`, `BooleanAnalysis.Hypercontractivity.low_norms_one_bit`, `BooleanAnalysis.Hypercontractivity.holder_ineq_bool`, `BooleanAnalysis.Hypercontractivity.hypercontractivity_induction`, `BooleanAnalysis.Hypercontractivity.holder_sharpness`, `BooleanAnalysis.expect_eq_fintypeExpect`.

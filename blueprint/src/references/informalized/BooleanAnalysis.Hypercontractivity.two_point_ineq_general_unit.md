<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/TwoPoint.lean :: BooleanAnalysis.Hypercontractivity.two_point_ineq_general_unit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unit two-point inequality for exponents

**Claim.** For $1\le p\le q\le2$ and $0\le b\le1$, with $\rho=\sqrt{(p-1)/(q-1)}$, the average of $(1+\rho b)^q$ and $(1-\rho b)^q$ is at most the $q/p$ power of the average of $(1+b)^p$ and $(1-b)^p$.

**Proof.** The proof separates the zero-exponent boundary cases first; under the remaining hypotheses the exponents are positive. Apply the integrated inequality (BooleanAnalysis.Hypercontractivity.integrated_h_alpha_ineq), which bounds the normalized increment of the left average from $1$ by the normalized increment of the right average from $1$. Let $X=((1+b)^p+(1-b)^p)/2$, which is nonnegative, and let $r=q/p\ge1$. The power lower bound $X^r\ge1+r(X-1)$ (BooleanAnalysis.Hypercontractivity.rpow_ge_one_add_mul_sub) converts the integrated inequality into the desired comparison: after multiplying by the positive exponents and rearranging, its right-hand side is precisely this tangent-line lower bound for $X^r$. The specified square root for $\rho$ supplies the parameter in the integrated inequality, and the remaining steps are algebraic rearrangements.

**Key facts.** `BooleanAnalysis.Hypercontractivity.integrated_h_alpha_ineq`, `BooleanAnalysis.Hypercontractivity.rpow_ge_one_add_mul_sub`.

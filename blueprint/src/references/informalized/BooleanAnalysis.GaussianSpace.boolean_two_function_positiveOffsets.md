<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/BooleanBounds.lean :: BooleanAnalysis.GaussianSpace.boolean_two_function_positiveOffsets -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Function Hypercontractive Inequality

**Claim.** Under the stated exponent and noise hypotheses, the inner product of $f$ with the noise operator applied to $g$ is bounded by the product of their respective $L^{1+r}$ and $L^{1+s}$ norms.

**Proof.** Split into two cases. If $r\le1$, the small-offset two-function inequality applies directly with the given hypotheses (`boolean_two_function_smallOffset`). If $r>1$, the condition $rs\le1$ and $r>1$ imply $s<1$, hence $s\le1$. By symmetry of the inner product and self-adjointness of the noise operator, $\langle f,T_\rho g\rangle=\langle g,T_\rho f\rangle$ (`innerProduct_comm`, `noiseOp_self_adjoint`). Apply the small-offset inequality with the roles of $f,g$ and $r,s$ exchanged; the product constraints on the exponents and the bound on $\rho^2$ are unchanged under this exchange. Reorder the two scalar norm factors to obtain the claimed bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.boolean_two_function_smallOffset`, `BooleanAnalysis.innerProduct_comm`, `BooleanAnalysis.noiseOp_self_adjoint`.

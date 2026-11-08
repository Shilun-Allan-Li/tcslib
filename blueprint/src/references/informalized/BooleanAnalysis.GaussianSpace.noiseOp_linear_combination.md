<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Noise.lean :: BooleanAnalysis.GaussianSpace.noiseOp_linear_combination -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linearity of the Boolean Noise Operator

**Claim.** For real numbers $\rho,c,d$ and Boolean functions $f,g$, the noise operator satisfies $T_\rho(cf+dg)=cT_\rho f+dT_\rho g$.

**Proof.** Fix an input $x$. Express the noise operator as a sum over inputs $y$, with each term the noise kernel at $(x,y)$ multiplied by the function value there (BooleanAnalysis.Hypercontractivity.noiseOp_eq_kernel_sum). Substituting $cf(y)+dg(y)$ into this sum, distribute the kernel over the two summands and use linearity of finite sums. Factoring out the constants $c$ and $d$ yields $cT_\rho f(x)+dT_\rho g(x)$. Since this holds for every $x$, the functions agree.

**Key facts.** `BooleanAnalysis.Hypercontractivity.noiseOp_eq_kernel_sum`.

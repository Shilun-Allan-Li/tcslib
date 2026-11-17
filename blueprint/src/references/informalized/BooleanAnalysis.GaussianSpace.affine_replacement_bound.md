<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Taylor.lean :: BooleanAnalysis.GaussianSpace.affine_replacement_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Replacement Bound

**Claim.** For two probability laws whose random variables have matching zero first and third moments, unit second moments, and fourth moments at most $9$, the difference between the expectations of $\psi(a+bX)$ and $\psi(a+bY)$ is at most $\frac{3C}{4}b^4$, when $\psi$ is four times continuously differentiable and its fourth derivative is bounded in absolute value by $C$.

**Proof.** Use the common second-order Taylor value $\psi(a)+(\psi''(a)/2)b^2$ as an intermediate quantity. The triangle inequality bounds the difference of the two expectations by the sum of their distances from this value. The fourth-order integral Taylor estimate (`abs_integral_sub_taylor_le`) bounds each distance by $(3C/8)b^4$, using the respective moment assumptions. Adding these two bounds gives $(3C/8)b^4+(3C/8)b^4=(3C/4)b^4.

**Key facts.** `BooleanAnalysis.GaussianSpace.abs_integral_sub_taylor_le`.

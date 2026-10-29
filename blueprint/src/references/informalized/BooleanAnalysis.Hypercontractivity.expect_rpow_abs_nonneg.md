<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/EvenMoments.lean :: BooleanAnalysis.Hypercontractivity.expect_rpow_abs_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Nonnegativity of an Expected Absolute Power on the Cube

**Claim.** For any real exponent $p$ and any Boolean function $f:\{0,1\}^n\to\mathbb{R}$, the expectation of $|f|^p$ under the uniform measure on the hypercube is nonnegative:
\[
\mathbb{E}\!\left[\,|f|^{\,p}\,\right] = 2^{-n}\sum_{x\in\{0,1\}^n}|f(x)|^{\,p} \;\ge\; 0,
\]
where the power is read with the conventions $0^0=1$ and $0^p=0$ for $p\neq 0$ (including negative $p$).

**Proof.** By definition the expectation is the product of the uniform weight $2^{-n}$ with the sum $\sum_{x\in\{0,1\}^n}|f(x)|^{\,p}$, so it is enough to see that both factors are nonnegative.

The weight $2^{-n}=(2^{-1})^n$ is a natural-number power of a nonnegative base, hence nonnegative. The remaining factor is a finite sum over the points of the cube, so it is nonnegative provided each summand is. Fix a point $x$. Its base $|f(x)|$ is an absolute value and therefore $\ge 0$, and the real power $t\mapsto t^{\,p}$ of a nonnegative base $t$ is again nonnegative under the stated conventions: if $|f(x)|>0$ then $|f(x)|^{\,p}=e^{p\ln|f(x)|}>0$ for every real $p$, while if $|f(x)|=0$ then $|f(x)|^{\,p}$ equals $1$ (when $p=0$) or $0$ (when $p\neq 0$), both $\ge 0$. Hence every summand is nonnegative, the sum is nonnegative, and a nonnegative constant times a nonnegative sum is nonnegative. This is the claim.

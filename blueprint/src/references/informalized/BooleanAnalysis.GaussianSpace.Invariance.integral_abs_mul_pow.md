<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/ThirdOrder.lean :: BooleanAnalysis.GaussianSpace.Invariance.integral_abs_mul_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Moment Factorization for Independent Products

**Claim.** For independent, almost everywhere measurable real random variables $U,V$ on a probability space, the integral of $|UV|^p$ factors as the product of the integrals of $|U|^p$ and $|V|^p$, for every natural number $p$.

**Proof.** Independence gives the product-integral formula for functions of the two variables: the integral of $f(U)g(V)$ is the product of the separate integrals when these compositions are almost everywhere strongly measurable. Take $f(t)=g(t)=|t|^p$. Since $|UV|^p=|U|^p|V|^p$, the formula gives the stated factorization.

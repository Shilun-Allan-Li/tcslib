<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Hoeffding.lean :: bernoulli_mgf_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bernoulli moment generating function bound

**Claim.** For $0\leq L\leq1$ and real $\eta$, $\ln(1-L+Le^{-\eta})\leq-L\eta+\eta^2/8$.

**Proof.** If $L=0$, the logarithm is $\log 1=0$ and the claim follows. If $L=1$, it is $\log(e^{-\eta})=-\eta$, again giving the bound. Now suppose $0<L<1$. The quantity $1-L+Le^{-x}$ is positive for every real $x$. Define $\varphi(x)=-Lx+x^2/8-\log(1-L+Le^{-x})$. The derivative formulas (bernoulli_mgf_bound_step1) and (bernoulli_mgf_bound_step2) give its first and second derivatives. The second derivative is nonnegative: after multiplying by the positive squared denominator, this is equivalent to $L(1-L)e^{-x}\leq(1-L+Le^{-x})^2/4$, which follows from the nonnegativity of $(1-L-Le^{-x})^2$. Thus $\varphi$ is convex. Its derivative at zero is zero, so convexity implies that it attains a minimum there; also $\varphi(0)=0$. Hence $\varphi(\eta)\geq0$, which rearranges to the desired inequality.

**Key facts.** `bernoulli_mgf_bound_step1`, `bernoulli_mgf_bound_step2`.

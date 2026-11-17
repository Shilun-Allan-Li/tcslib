<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Exponential.lean :: BooleanAnalysis.GaussianSpace.tendsto_gaussian_exp_taylor -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Taylor convergence in $L^p$

**Claim.** For every finite exponent $p$ and continuous real-linear map $L:\mathbb R^n\to\mathbb C$, the $L^p(\gamma_n)$ quasi-norm of the error between $e^{L(x)}$ and its degree-$(k-1)$ Taylor polynomial tends to zero as $k\to\infty.

**Proof.** If $p=0$, the exponent-zero identity makes every displayed quasi-norm equal to zero. For $0<p<\infty$, apply dominated convergence in the form that turns pointwise convergence to zero, together with a common $L^p$ majorant, into convergence of the $L^p$ quasi-norms. Each Taylor remainder is continuous, hence measurable. Pointwise, the exponential series converges, so the remainders tend to zero. For domination, the norm of the complex remainder is at most $e^{\|Lx\|}$: the Taylor remainder estimate bounds it by the real exponential minus a sum of nonnegative terms, which is at most the exponential itself. The operator norm bound gives $\|Lx\|\le \|L\|\|x\|$, and on the coordinate space $\|x\|\le\sum_i|x_i|$. Thus the remainders are bounded by $\exp(\|L\|\sum_i|x_i|)$, which belongs to $L^p(\gamma_n)$ by the Gaussian exponential-integrability lemma (memLp_exp_sum_abs_gaussian). The dominated-convergence conclusion (tendsto_eLpNorm_zero_of_dominated) now gives the result.

**Key facts.** `BooleanAnalysis.GaussianSpace.memLp_exp_sum_abs_gaussian`, `BooleanAnalysis.GaussianSpace.tendsto_eLpNorm_zero_of_dominated`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basis.lean :: BooleanAnalysis.GaussianSpace.hermiteFunction_memLp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-order integrability of Hermite functions

**Claim.** For every natural number $n$, multi-index $\alpha:\{1,\ldots,n\}\to\mathbb N$, and exponent $p\in[0,\infty]$ with $p\ne\infty$, the Hermite function indexed by $\alpha$ belongs to $L^p$ for the product of $n$ standard Gaussian measures.

**Proof.** The multivariate Hermite polynomial indexed by $\alpha$ is a polynomial in the $n$ coordinates, and the Hermite function is its evaluation at the point. The Gaussian polynomial integrability result `memLp_eval_gaussian` says that evaluating any such polynomial belongs to $L^p$ under the product Gaussian measure whenever $p\ne\infty$. Applying it to the multivariate Hermite polynomial gives the assertion.

**Key facts.** `BooleanAnalysis.GaussianSpace.memLp_eval_gaussian`.

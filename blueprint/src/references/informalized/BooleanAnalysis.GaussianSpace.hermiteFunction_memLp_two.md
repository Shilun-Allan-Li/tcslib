<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basis.lean :: BooleanAnalysis.GaussianSpace.hermiteFunction_memLp_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square integrability of Hermite functions

**Claim.** For every natural number $n$ and multi-index $\alpha:\{1,\ldots,n\}\to\mathbb N$, the Hermite function indexed by $\alpha$ belongs to $L^2$ for the product of $n$ standard Gaussian measures.

**Proof.** Apply the finite-order integrability result for Hermite functions (`hermiteFunction_memLp`) with exponent $p=2$. This exponent is finite, so the required hypothesis $p\ne\infty$ holds.

**Key facts.** `BooleanAnalysis.GaussianSpace.hermiteFunction_memLp`.

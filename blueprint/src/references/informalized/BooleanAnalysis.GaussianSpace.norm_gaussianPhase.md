<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Fourier.lean :: BooleanAnalysis.GaussianSpace.norm_gaussianPhase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unit modulus of the Gaussian phase

**Claim.** For every natural number $n$, every $a\in\mathbb R$, and every $x,y\in\mathbb R^n$, the complex phase $\exp\!\left(i a\sum_{j=1}^n x_jy_j\right)$ has modulus $1$.

**Proof.** The exponent is purely imaginary: it is $i$ times the real number $a\sum_j x_jy_j$. The complex exponential of a purely imaginary number has norm $1$, so the stated phase has modulus $1$.

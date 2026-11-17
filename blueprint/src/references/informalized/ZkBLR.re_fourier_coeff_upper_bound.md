<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkBLR.lean :: ZkBLR.re_fourier_coeff_upper_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pointwise Fourier Coefficient Bound

**Claim.** For $k\ge2$, the real part of the Fourier coefficient of the lift of $f$ at frequency $s$ is at most $1-(1-\cos(2\pi/k))$ times the fraction of inputs where $f(x)$ differs from $s\cdot x$.

**Proof.** For each input $x$, consider the product of the lifted value at $f(x)$ with the conjugate of the lifted value at $s\cdot x$. If the two values agree, this product is a root of unity times its conjugate, hence equals $1$. If they disagree, their difference in $\mathbb Z/k\mathbb Z$ is nonzero. The real part of its lifted root of unity is at most $\cos(2\pi/k)$, by the bound for nontrivial roots of unity; the product in question is that lifted difference, using multiplicativity of the lift and the fact that negation corresponds to complex conjugation. Thus in both cases its real part is at most $1-(1-\cos(2\pi/k))$ times the disagreement indicator. Sum this inequality over all inputs and divide by the size $k^n$ of the domain. The left side is the real part of the Fourier coefficient, and the normalized disagreement count is the stated distance.

**Key facts.** `ZkBLR.re_toOmega_le_re_rootOfUnity`, `ZkFourier.toOmega_add`, `ZkFourier.toOmega_neg`.

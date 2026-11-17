<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.polynomialThresholdRepresentation_hasThresholdOfThresholdsSizeAtMost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold Composition Size Bound

**Claim.** Let $n$ be a natural number, let $f:\{−1,1\}^n\to\{−1,1\}$, and let $p:\{−1,1\}^n\to\mathbb R$. Suppose $f(x)=1$ when $p(x)\geq0$ and $f(x)=-1$ when $p(x)<0$. Then $f$ can be expressed as a threshold of at most $2n\,s$ linear threshold functions, where $s$ is the number of nonzero Fourier coefficients of $p$ on the Boolean cube.

**Proof.** The polynomial threshold representation theorem supplies a threshold-of-thresholds representation using exactly $s(2n)$ linear threshold gates, where $s$ is the size of the Fourier support of $p$ (\texttt{FABL.polynomialThresholdRepresentation_isThresholdOfThresholds}). By definition, this support size is the polynomial sparsity. Since $s(2n)=2ns$, this representation witnesses the claimed size bound.

**Key facts.** `FABL.polynomialThresholdRepresentation_isThresholdOfThresholds`.

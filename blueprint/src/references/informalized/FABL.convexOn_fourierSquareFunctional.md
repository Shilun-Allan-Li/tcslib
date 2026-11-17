<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/FourierSquareConvexity.lean :: FABL.convexOn_fourierSquareFunctional -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convexity of the Fourier square functional

**Claim.** For a natural number $n$, let $c$ assign a real number $c(S)$ to each subset $S$ of $\{1,\ldots,n\}$, with $c(S)\ge 0$ for every $S$. On the space of real-valued functions on $\{-1,1\}^n$, the functional sending $f$ to $\sum_S c(S)\widehat f(S)^2$ is convex.

**Proof.** Take functions $f,g$ and a convex weight $a\in[0,1]$. The other weight is then $1-a$. The affine inequality for the Fourier square functional says that its value at the pointwise combination $af+(1-a)g$ is at most $a$ times its value at $f$ plus $1-a$ times its value at $g$, provided all coefficients $c(S)$ are nonnegative. This is precisely convexity.

**Key facts.** `FABL.fourierSquareFunctional_affine_le`.

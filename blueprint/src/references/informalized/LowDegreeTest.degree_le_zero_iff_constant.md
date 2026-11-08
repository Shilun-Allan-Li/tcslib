<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.degree_le_zero_iff_constant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree zero means constant

**Claim.** A Boolean function has degree at most zero if and only if it is constant.

**Proof.** Suppose first that the function has degree at most zero. Its first-order derivative condition, applied at $x$ in direction $x\oplus y$, says that the sign lift at $x$ times its value at $x\oplus(x\oplus y)$ is $1$. Since $x\oplus(x\oplus y)=y$ and both sign values are in $\{\pm1\}$, this forces the values at $x$ and $y$ to agree. Conversely, if $f$ is constant, then for every point $x$ and direction $h$ the values at $x$ and $x\oplus h$ agree. Their sign lifts multiply to the square of a sign, which is $1$. Hence the function has degree at most zero.

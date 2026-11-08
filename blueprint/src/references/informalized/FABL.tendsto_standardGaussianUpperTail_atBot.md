<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.tendsto_standardGaussianUpperTail_atBot -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper tail at negative infinity

**Claim.** As $t$ tends to $-\infty$, the standard Gaussian upper tail tends to $1$.

**Proof.** The standard Gaussian upper tail is $1-F(t)$, where $F$ is its cumulative distribution function. As $t\to-\infty$, the cumulative distribution function tends to $0$. Subtracting a function tending to $0$ from the constant $1$ gives a limit of $1$.

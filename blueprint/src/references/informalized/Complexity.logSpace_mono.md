<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Basic.lean :: Complexity.logSpace_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the logarithmic bound

**Claim.** If $a,b\in\mathbb{N}$ and $a\le b$, then $\ell(a)\le\ell(b)$, where $\ell(n)=\lfloor\log_2 n\rfloor+1$ for positive $n$ and $\ell(0)=1$.

**Proof.** The floor logarithm with base $2$ is monotone in its argument, so $a\le b$ implies $\lfloor\log_2 a\rfloor\le\lfloor\log_2 b\rfloor$. Adding one to both sides yields the claimed inequality for $\ell$.

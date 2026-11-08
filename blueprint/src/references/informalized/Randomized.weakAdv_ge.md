<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.weakAdv_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound for Weak Advantage

**Claim.** For natural numbers $c$ and $n$, $((n+1)^{-1})^c/6$ is at most the weak advantage $\min\{1/6,((n+1)^{-1})^c\}$.

**Proof.** Set $y=((n+1)^{-1})^c$. Since $n+1$ is positive, its reciprocal is positive, so $y\ge 0$. Also $(n+1)^{-1}\le 1$; raising this nonnegative quantity to the natural power $c$ gives $y\le 1$. Thus $y/6\le 1/6$ and $y/6\le y$. It is therefore bounded above by both entries in the minimum, hence by their minimum.

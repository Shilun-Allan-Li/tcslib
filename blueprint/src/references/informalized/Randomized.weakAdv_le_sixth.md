<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.weakAdv_le_sixth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weak Advantage Bound

**Claim.** For natural numbers $c$ and $n$, the weak advantage $\min\{1/6,((n+1)^{-1})^c\}$ is at most $1/6$.

**Proof.** By definition, the weak advantage is the minimum of $1/6$ and $((n+1)^{-1})^c$. A minimum is at most either of its arguments, so it is at most $1/6$.

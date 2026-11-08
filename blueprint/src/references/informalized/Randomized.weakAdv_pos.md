<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.weakAdv_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of Weak Advantage

**Claim.** For natural numbers $c$ and $n$, the weak advantage $\min\{1/6,((n+1)^{-1})^c\}$ is positive.

**Proof.** Both entries of the minimum are positive: $1/6>0$, and $n+1$ is positive, so its reciprocal and every natural power of that reciprocal are positive. The minimum of two positive numbers is positive.

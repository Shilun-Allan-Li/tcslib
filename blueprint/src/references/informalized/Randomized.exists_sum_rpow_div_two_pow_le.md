<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.exists_sum_rpow_div_two_pow_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Exponentially Weighted Power Sums

**Claim.** For every real $c$, there is a real constant $D$ such that for every natural number $n\geq1$, $\sum_{i=1}^{n} i^c/2^i\leq D$.

**Proof.** Let $k=\lceil c\rceil$. For every integer $i\geq1$, the base $i$ is at least one and $c\leq k$, so $i^c\leq i^k$. The series $\sum_{i\geq0}i^k(1/2)^i$ converges, since a polynomially weighted geometric series converges whenever the geometric ratio has absolute value less than one. Take its sum as $D$. Each term of the finite sum is bounded by the corresponding term of this convergent nonnegative series, so every indicated partial sum is at most $D$.

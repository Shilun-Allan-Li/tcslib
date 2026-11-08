<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.one_sub_pow_le_half_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Powered Exponential Bound

**Claim.** If $x$ is rational with $0\le x\le1$ and natural numbers $m,T,e$ satisfy $mx\ge1$ and $mT\le e$, then $(1-x)^e\le(1/2)^T$.

**Proof.** Because $0\le1-x\le1$ and $mT\le e$, increasing the exponent from $mT$ to $e$ cannot increase the power, so $(1-x)^e\le(1-x)^{mT}$. The latter is $((1-x)^m)^T$. The exponential probability bound gives $(1-x)^m\le1/2$ from $mx\ge1$; raising both nonnegative sides to the natural power $T$ preserves the inequality. Combining these inequalities proves the result.

**Key facts.** `Randomized.one_sub_pow_le_half`.

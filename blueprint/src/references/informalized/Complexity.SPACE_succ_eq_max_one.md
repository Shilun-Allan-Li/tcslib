<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ZeroSpace.lean :: Complexity.SPACE_succ_eq_max_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor and maximum space bounds

**Claim.** For every function $s:\mathbb{N}\to\mathbb{N}$, the class of binary languages decidable with space bounded by a constant multiple of $s(n)+1$ equals the class decidable with space bounded by a constant multiple of $\max(1,s(n))$.

**Proof.** For the inclusion from the successor bound to the maximum bound, note pointwise that $s(n)+1\le 2\max(1,s(n))$. Monotonicity under constant scaling therefore gives the inclusion (Complexity.SPACE.mono_const). In the other direction, $\max(1,s(n))\le s(n)+1$ for every $n$, so ordinary monotonicity gives the reverse inclusion (Complexity.SPACE.mono). The two inclusions establish equality.

**Key facts.** `Complexity.SPACE.mono_const`, `Complexity.SPACE.mono`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ZeroSpace.lean :: Complexity.SPACE_succ_of_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive bounds and their successors

**Claim.** If $s(n)>0$ for every $n$, then the class of binary languages decidable with space bounded by a constant multiple of $s(n)$ equals the class decidable with space bounded by a constant multiple of $s(n)+1$.

**Proof.** Since $s(n)\le s(n)+1$, monotonicity gives $\mathrm{SPACE}(s)\subseteq\mathrm{SPACE}(s+1)$ (Complexity.SPACE.mono). Conversely, positivity and integrality imply $s(n)\ge1$, hence $s(n)+1\le2s(n)$. Monotonicity under constant scaling gives $\mathrm{SPACE}(s+1)\subseteq\mathrm{SPACE}(s)$ (Complexity.SPACE.mono_const). Together these yield equality.

**Key facts.** `Complexity.SPACE.mono`, `Complexity.SPACE.mono_const`.

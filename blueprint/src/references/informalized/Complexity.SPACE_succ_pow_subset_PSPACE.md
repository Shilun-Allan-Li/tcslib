<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMWidth.lean :: Complexity.SPACE_succ_pow_subset_PSPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shifted power space is polynomial space

**Claim.** For every natural number $k$, the class of binary languages decidable with space bounded by a constant multiple of $(n+1)^k$ is contained in polynomial space.

**Proof.** For each $n$, the elementary estimate $(n+1)^k\le 2^k(n^k+1)$ holds (Complexity.succ_pow_le). Monotonicity under constant scaling therefore places $\mathrm{SPACE}((n+1)^k)$ inside $\mathrm{SPACE}(n^k+1)$ (Complexity.SPACE.mono_const). The polynomial-space containment theorem places this latter class inside $\mathrm{PSPACE}$ (Complexity.space_poly_subset_PSPACE). Composing the inclusions proves the claim.

**Key facts.** `Complexity.succ_pow_le`, `Complexity.SPACE.mono_const`, `Complexity.space_poly_subset_PSPACE`.

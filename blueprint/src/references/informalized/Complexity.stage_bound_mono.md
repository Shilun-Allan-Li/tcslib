<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.stage_bound_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of stage bounds

**Claim.** For every sequence $N$ of finite oracle Turing machines and natural numbers $i\le j$, the bound at stage $i$ is at most the bound at stage $j$.

**Proof.** Use induction along the stages from $i$ to $j$. At the initial stage the two bounds are equal. For the successor step, the next bound is the maximum of the fresh length chosen from the current bound and the current stage index raised to that fresh length, plus the index (`Complexity.stage_bound_succ`). The fresh length is strictly greater than the current bound by `Complexity.freshLen_spec`; hence the maximum, and therefore the next bound, is at least the current bound. This proves the induction step and the claim.

**Key facts.** `Complexity.stage_bound_succ`, `Complexity.freshLen_spec`.

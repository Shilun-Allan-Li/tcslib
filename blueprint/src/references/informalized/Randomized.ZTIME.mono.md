<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.ZTIME.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of zero-error time

**Claim.** If $T_1(n)\le T_2(n)$ for every $n$, then every language decidable in zero-error expected time bounded by $T_1$ is also decidable in zero-error expected time bounded by $T_2$.

**Proof.** A witness for membership in `ZTIME T₁` consists of a constant $c$, a machine, and its zero-error time bound. Keep the same constant and machine. For each input length $n$, the hypothesis gives $T_1(n)\le T_2(n)$, so multiplication by $c$ gives $cT_1(n)\le cT_2(n)$. Thus every finite partial sum of the machine's non-halting probabilities up to the former bound is at most the corresponding sum up to the latter bound, since the summands are nonnegative. The correctness condition on halted runs is unchanged. Hence the same machine witnesses membership in `ZTIME T₂`.

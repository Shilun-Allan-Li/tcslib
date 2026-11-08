<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTM.lean :: Randomized.BPTIME.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Randomized Time

**Claim.** If $T_1(n)\le T_2(n)$ for every input length, then every language decidable with bounded error in time bounded by a constant multiple of $T_1$ is also decidable with bounded error in time bounded by the same constant multiple of $T_2$.

**Proof.** Take a witness for membership in the first class: a constant $c$, a machine, and its bounded-error time-deciding property. Multiplying the pointwise inequality $T_1(n)\le T_2(n)$ by $c$ gives $cT_1(n)\le cT_2(n)$. The time monotonicity theorem for bounded-error decidability preserves the machine and its correctness guarantee while enlarging the time bound (`Turing.FinNDTM.BPDecidesInTime.mono`). Thus the same witness establishes membership in the second class.

**Key facts.** `Turing.FinNDTM.BPDecidesInTime.mono`.

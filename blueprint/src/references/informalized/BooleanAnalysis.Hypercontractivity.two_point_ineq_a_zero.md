<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/OneBit.lean :: two_point_ineq_a_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The degenerate case of the two-point inequality

**Claim.** For real `p` with `1 ≤ p ≤ 2`, the real power `(p - 1) ^ (p / 2)` is at
most `1`. (The exponent is `Real.rpow`, not a natural-number power.)

**Proof.** One line: `exact Real.rpow_le_one (by linarith) (by linarith) (by linarith)`.
The three side conditions are all immediate from `1 ≤ p ≤ 2`:

- base nonnegative: `0 ≤ p - 1`;
- base at most one: `p - 1 ≤ 1`;
- exponent nonnegative: `0 ≤ p / 2`.

**Used in.** No direct TCSlib use sites are recorded in the current compiler-derived dependency graph.

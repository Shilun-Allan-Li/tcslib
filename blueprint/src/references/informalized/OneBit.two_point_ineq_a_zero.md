<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/OneBit.lean :: two_point_ineq_a_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The degenerate case of the two-point inequality

**Claim.** For real `p` with `1 ≤ p ≤ 2`, the real power `(p - 1) ^ (p / 2)` is at
most `1`. (The exponent is `Real.rpow`, not a natural-number power.)

**Proof.** One line: `exact Real.rpow_le_one (by linarith) (by linarith) (by linarith)`.
The three side conditions are all immediate from `1 ≤ p ≤ 2`:

- base nonnegative: `0 ≤ p - 1`;
- base at most one: `p - 1 ≤ 1`;
- exponent nonnegative: `0 ≤ p / 2`.

**Used in.** Nothing. The lemma is a granular helper, named for the `a = 0`
specialisation of `two_point_ineq` — where the claim
`(a² + ρ²b²)^{1/2} ≤ ((|a+b|^p + |a-b|^p)/2)^{1/p}` degenerates to a statement
about `(p-1)^{p/2}` — but `two_point_ineq` in fact dispatches `a = 0` inline
(`simp_all` plus `Real.zero_rpow`) and never calls this lemma. No other
declaration in the repository references it either; it is dead code retained for
documentation of the case split.

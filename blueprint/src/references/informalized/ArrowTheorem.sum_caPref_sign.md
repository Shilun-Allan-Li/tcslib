<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ArrowTheorem.lean :: sum_caPref_sign -->
<!-- origin: boolean-ch02-social-choice-arrow run 352ab7ff3113 verdict not_in_text (0.72) -->

# The c-vs-a marginal is balanced over the six orderings

**Claim.** Summing the ±1-encoded c-vs-a preference over all six transitive
orderings of `{a,b,c}` gives zero: `∑ k : Fin 6, boolToSign (caPref k) = 0`.
Here `caPref k` is `true` when ordering `k` ranks `a` above `c`, and
`boolToSign b = if b then -1 else 1`.

**Proof.**

1. `Fin.sum_univ_six` expands the sum over `Fin 6` into its six explicit
   summands, one per ordering.
2. Unfolding `caPref` evaluates the six cases to
   `true, true, true, false, false, false` (orderings `a>b>c`, `a>c>b`,
   `b>a>c`, `b>c>a`, `c>a>b`, `c>b>a`).
3. Unfolding `boolToSign` turns these into `-1, -1, -1, 1, 1, 1`, and
   `norm_num` adds them to `0`.

**Remark.** The third of the three marginal facts, for the closing comparison
of the cycle; unlike the other two its `true`/`false` blocks are contiguous
(orderings `0, 1, 2` rank `a` above `c`, orderings `3, 4, 5` rank `c` above
`a`). It supplies `hy` to `profile_kernel_gen` in `profile_kernel_bcca` and
`profile_kernel_abca`.

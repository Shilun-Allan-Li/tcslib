<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ArrowTheorem.lean :: sum_bcPref_sign -->
<!-- origin: boolean-ch02-social-choice-arrow run 352ab7ff3113 verdict not_in_text (0.82) -->

# The b-vs-c marginal is balanced over the six orderings

**Claim.** Summing the ±1-encoded b-vs-c preference over all six transitive
orderings of `{a,b,c}` gives zero: `∑ k : Fin 6, boolToSign (bcPref k) = 0`.
Here `bcPref k` is `false` when ordering `k` ranks `b` above `c`, and
`boolToSign b = if b then -1 else 1`.

**Proof.**

1. `Fin.sum_univ_six` expands the sum over `Fin 6` into its six explicit
   summands, one per ordering.
2. Unfolding `bcPref` evaluates the six cases to
   `false, true, false, false, true, true` (orderings `a>b>c`, `a>c>b`,
   `b>a>c`, `b>c>a`, `c>a>b`, `c>b>a`).
3. Unfolding `boolToSign` turns these into `1, -1, 1, 1, -1, -1`, and
   `norm_num` adds them to `0`.

**Remark.** Same shape as `sum_abPref_sign` but for the second comparison pair:
here the split is orderings `0, 2, 3` preferring `b` against `1, 4, 5`
preferring `c`. It is the `hx`/`hy` input to `profile_kernel_gen` for the
`ab`–`bc` and `bc`–`ca` kernels.

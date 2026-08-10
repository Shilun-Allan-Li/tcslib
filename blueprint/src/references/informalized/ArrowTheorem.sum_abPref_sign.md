<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ArrowTheorem.lean :: sum_abPref_sign -->
<!-- origin: boolean-ch02-social-choice-arrow run 352ab7ff3113 verdict not_in_text (0.83) -->

# The a-vs-b marginal is balanced over the six orderings

**Claim.** Summing the ±1-encoded a-vs-b preference over all six transitive
orderings of `{a,b,c}` gives zero: `∑ k : Fin 6, boolToSign (abPref k) = 0`.
Here `abPref k` is `false` when ordering `k` ranks `a` above `b`, and
`boolToSign b = if b then -1 else 1`.

**Proof.**

1. `Fin.sum_univ_six` expands the sum over `Fin 6` into its six explicit
   summands, one per ordering.
2. Unfolding `abPref` evaluates the six cases to
   `false, false, true, true, false, true` (orderings `a>b>c`, `a>c>b`,
   `b>a>c`, `b>c>a`, `c>a>b`, `c>b>a`).
3. Unfolding `boolToSign` turns these into `1, 1, -1, -1, 1, -1`, and
   `norm_num` adds them to `0`.

**Remark.** The three orderings ranking `a` above `b` are exactly balanced by
the three ranking `b` above `a`; this is the `ab` member of a triple of
identical marginal facts (`sum_bcPref_sign`, `sum_caPref_sign`). It supplies
the `hx`/`hy` hypotheses of `profile_kernel_gen`, which is what makes the
off-diagonal Fourier kernel vanish in `profile_inner_product_kernel` and
`profile_kernel_abca`.

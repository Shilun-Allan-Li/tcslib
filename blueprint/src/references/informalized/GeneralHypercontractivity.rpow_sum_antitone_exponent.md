<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: rpow_sum_antitone_exponent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The symmetric power sum is antitone in a non-positive exponent

**Claim.** For `0 < x < 1` and real exponents `p ≤ q ≤ 0`,
`(1 + x) ^ p + (1 - x) ^ p ≥ (1 + x) ^ q + (1 - x) ^ q` (real `rpow`). So on the
non-positive range the map `t ↦ (1+x)^t + (1-x)^t` is decreasing.

**Proof.** By contradiction (`by_contra!`), assuming the strict reverse inequality.

1. Put `f t = (1 + x) ^ t + (1 - x) ^ t` (`set f`).
2. `deriv f t ≤ 0` for every `t < 0`: rewrite both powers with
   `Real.rpow_def_of_pos` (both bases are positive since `0 < x < 1`), then use
   `Real.exp_le_one_iff` and `Real.one_le_exp` to get
   `exp (t log (1+x)) ≤ 1 ≤ exp (t log (1-x))`, and close with `nlinarith` on
   `Real.log_le_sub_one_of_pos` plus positivity of the two exponentials.
3. Mean value theorem on `[p, q]` (`exists_deriv_eq_slope`, with continuity from
   `ContinuousAt.rpow` and differentiability from `DifferentiableOn.rpow`) gives
   `c ∈ (p, q)` with `deriv f c = (f q - f p) / (q - p)`.
4. `c < q ≤ 0`, so step 2 applies at `c`; `div_le_iff₀` then forces
   `f q ≤ f p`, contradicting the assumption. ∎

**Note.** The hypothesis `_hp0 : p ≤ 0` is unused (only `q ≤ 0` is needed, since
`c < q`). The comment block above the lemma in the source describes a different
statement ("for `0 < b < 1`, `α ↦ b^α` is convex") and does not match what is proved.

**Used in.** `h_alpha_ineq` (step `h_ineq_step1`), the derivative inequality behind
the general one-bit two-point inequality.

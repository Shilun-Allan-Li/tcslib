<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: inner_shifted_le_expr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Shifted inner product is bounded by the code parameters

**Claim.** Let `α ≥ 0` and `x y : BitVec n` with `d ≤ hdist x y`,
`wt x ≤ w` and `wt y ≤ w`. Then

`⟪shifted α x, shifted α y⟫_[ℝ] ≤ (n - 2*d) + α^2 * n + 2*α*(2*w - n)`.

The bound depends on `x` and `y` only through the parameters `n`, `d`, `w`.

**Proof.**

1. First compute the exact value: by `inner_shifted_expand` followed by
   `inner_pmOne_pmOne`, `inner_pmOne_ones` and `inner_ones_ones`
   (applied with `erw`, then `norm_num; ring_nf`),

   `⟪shifted α x, shifted α y⟫ = (n - 2*hdist x y) - α*(n - 2*wt x) - α*(n - 2*wt y) + α^2*n`.

2. `nlinarith` then closes the inequality from the three hypotheses cast to ℝ
   (`norm_cast`: `d ≤ hdist x y`, `wt x ≤ w`, `wt y ≤ w`) together with
   `0 ≤ α`: the distance hypothesis gives `n - 2*hdist x y ≤ n - 2*d`, and each
   weight hypothesis multiplied by the nonnegative `α` gives
   `-α*(n - 2*wt ·) ≤ α*(2*w - n)`.

**Used in.** `binary_johnson_card_bound_parametric`, where it supplies the
pairwise non-positivity of inner products (via the hypothesis `harith`) needed
to apply `rankin_finset_bound`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: johnson_arith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The Johnson choice of `α` makes the bound non-positive

**Claim.** Let `0 < n`, `2*d ≤ n` and `(w : ℝ) ≤ J2 n d`, where
`J2 n d = (n - √(n*(n - 2*d)))/2`. Then, for `α = alpha n d = √((n - 2*d)/n)`,

`(n - 2*d) + α^2 * n + 2*α*(2*w - n) ≤ 0`.

This is the arithmetic fact that the parametric bound degenerates exactly at
the Johnson radius.

**Proof.**

1. Unfolding `J2` in the hypothesis and `linarith` give
   `2*w ≤ n - √(n*(n - 2*d))`.
2. `alpha n d` is `√((n - 2*d)/n)` by `rfl`, so `Real.sq_sqrt` — with
   non-negativity of the radicand from `sub_nonneg` on `2*d ≤ n` and
   `Nat.cast_nonneg` — gives `α^2 = (n - 2*d)/n`, hence `α^2 * n = n - 2*d`.
3. `Real.sqrt_div` rewrites `α` as `√(n - 2*d)/√n`, and `Real.sqrt_mul`
   rewrites the hypothesis' radical as `√n * √(n - 2*d)`.
4. After `field_simp`, `nlinarith` concludes from `Real.mul_self_sqrt` for
   `√n` and `√(n - 2*d)` plus the `positivity` facts `0 ≤ √n`,
   `0 ≤ √(n - 2*d)`: the left side is `2*(n - 2*d) + 2*α*(2*w - n)`, and
   step 1 bounds `2*w - n ≤ -√n*√(n - 2*d)`, whose product with
   `α = √(n - 2*d)/√n` contributes exactly `-2*(n - 2*d)`.

**Used in.** `binary_johnson_card_bound`, to discharge the `harith`
hypothesis of `binary_johnson_card_bound_parametric` at `α = alpha n d`.

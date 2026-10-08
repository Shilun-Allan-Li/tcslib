<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/TwoPoint.lean :: rpow_ge_one_add_mul_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Tangent-line inequality for `x ↦ x^r` at `x = 1`

**Claim.** For real `x ≥ 0` and `r ≥ 1`, `x ^ r ≥ 1 + r * (x − 1)` (real `rpow`).
The convex function `x^r` lies above its tangent line at `x = 1`.

**Proof.** From weighted AM–GM rather than differentiation.

1. `Real.geom_mean_le_arith_mean` is specialized to the two-element index set
   `{0, 1}` with weights `(1, r − 1)` — nonnegative by `hr` — and values
   `(x ^ r, 1)`, both nonnegative by `positivity`.
2. The geometric-mean side is `(x^r) ^ (1/r) · 1 ^ ((r−1)/r)`, which collapses to
   `x` by `← Real.rpow_mul`, `mul_inv_cancel₀` and `Real.rpow_one`.
3. Clearing the total weight `r` from the arithmetic-mean side
   (`le_div_iff₀`) leaves `r · x ≤ x^r + (r − 1)`, and `nlinarith` rearranges this
   into the claim.

**Used in.** `BooleanAnalysis.Hypercontractivity.two_point_ineq_general_unit` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/TwoPoint.lean`.

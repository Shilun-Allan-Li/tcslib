<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Simple.lean :: innerProduct_le_L43_L4 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Hölder's inequality at the exponent pair (4/3, 4)

**Claim.** For `f g : BooleanFunc n`,

`innerProduct f g ≤ (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) * (expect (fun x => |g x| ^ 4)) ^ (1/4 : ℝ)`,

i.e. `⟪f, g⟫ ≤ ‖f‖_{4/3} · ‖g‖₄` for the uniform measure on the cube.

**Proof.** Unfold `innerProduct`, `expect`, `uniformWeight`, so both sides are
sums against the constant weight `(2⁻¹)^n`, then run a `calc` chain.

1. `h_abs`: `f x * g x ≤ |f x| * |g x|` pointwise (`le_abs_self`, `abs_mul`),
   summed by `Finset.sum_le_sum`; `h_weight_abs` multiplies through by the
   nonnegative weight (`mul_le_mul_of_nonneg_left`).
2. `holder_sum`: with `p := 4/3`, `q := 4` and `hpq : HolderConjugate p q`
   (all three fields by `norm_num`), Mathlib's
   `inner_le_Lp_mul_Lq_of_nonneg` gives
   `∑ |f x| |g x| ≤ (∑ |f x|^p)^{1/p} (∑ |g x|^q)^{1/q}`.
3. `weight_split`: the weight factors as
   `(2⁻¹)^n = ((2⁻¹)^n)^{1/p} · ((2⁻¹)^n)^{1/q}`, since `1/p + 1/q = 1`
   (`← Real.rpow_add`, `Real.rpow_one`).
4. Regroup each weight factor with its own sum (`ring`), then pull it inside the
   rpow via `← Real.mul_rpow` (legal since both sums are nonneg by
   `Finset.sum_nonneg`), turning `(2⁻¹)^n * ∑ …` back into `expect`.
5. Finally `1/p = 3/4` and `1/q = 1/4` by `norm_num`, and
   `Real.rpow_natCast` reconciles the real exponent `|g x| ^ (4:ℝ)` with the
   natural-power `|g x| ^ (4:ℕ)` in the statement; `rfl` closes. ∎

**Used in.** `hypercontractivity_4_div_3_2`, where it is paired with
`noiseOp_self_adjoint` and `hypercontractivity_2_4` to dualise the (2,4) bound
into a (4/3, 2) bound.

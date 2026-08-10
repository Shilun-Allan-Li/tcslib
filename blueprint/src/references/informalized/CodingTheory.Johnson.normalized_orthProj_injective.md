<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: normalized_orthProj_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Two obtuse unit vectors cannot share a normalized projection

**Claim.** Let `u v w : V` be unit vectors in a real inner product space with
`inner ℝ v u ≤ 0`, `inner ℝ w u ≤ 0`, `inner ℝ v w ≤ 0`, and `v, w ∉ {u, -u}`
(plus `v ≠ w`). If `‖orthProj u v‖⁻¹ • orthProj u v = ‖orthProj u w‖⁻¹ • orthProj u w`,
then `False`.

**Proof.**

1. Both projections are non-zero (`orthProj_ne_zero`), so scaling `h_eq` by
   `‖orthProj u v‖` gives `c > 0` with `orthProj u v = c • orthProj u w`, where
   `c = ‖orthProj u v‖ / ‖orthProj u w‖` (`div_pos`, `norm_pos_iff`,
   `mul_inv_cancel₀`).
2. Substituting `v = c • (w - ⟪u,w⟫ • u) + ⟪u,v⟫ • u` (from step 1 via
   `sub_add_cancel`) and expanding with `inner_add_left`, `inner_sub_left`,
   `inner_smul_left` plus `real_inner_self_eq_norm_sq` and `‖w‖ = 1` gives
   `⟪v, w⟫ = c * (1 - ⟪u,w⟫^2) + ⟪u,v⟫ * ⟪u,w⟫`.
3. `|⟪u, w⟫| < 1`: since `w ≠ u` and `w ≠ -u`, both `‖w - u‖ > 0` and
   `‖w + u‖ > 0` (`sub_ne_zero`, `add_eq_zero_iff_eq_neg`), and
   `norm_add_sq_real` / `norm_sub_sq_real` turn these into the two strict
   inequalities `abs_lt` needs (`nlinarith`).
4. Then `c * (1 - ⟪u,w⟫^2) > 0` while `⟪u,v⟫ * ⟪u,w⟫ ≥ 0`, so step 2 forces
   `⟪v, w⟫ > 0`, contradicting `hvw_ip` (`nlinarith [abs_lt.mp h_abs,
   mul_le_mul_of_nonneg_left hwu hc.1.le]`).

**Used in.** `rankin_bound_general` step 2, where it supplies
`Finset.card_image_of_injOn` for the map `mkProj u`, so the filtered set `T` and
its image `T'` in `(span ℝ {u})ᗮ` have the same cardinality.

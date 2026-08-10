<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: orthProj_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `orthProj u v` vanishes only when `v = ±u`

**Claim.** For unit vectors `u v : V` (`‖u‖ = 1`, `‖v‖ = 1`) with `v ≠ u` and
`v ≠ -u`, we have `orthProj u v ≠ 0`, i.e. `v - (inner ℝ u v) • u ≠ 0`.

**Proof.** `by_contra h_contra`, assuming the projection is `0`.

1. `eq_of_sub_eq_zero` gives `v = (inner ℝ u v) • u`.
2. Applying `congr_arg Norm.norm` and simplifying with `norm_smul` together with
   `‖u‖ = ‖v‖ = 1` yields `|inner ℝ u v| = 1`.
3. `eq_or_eq_neg_of_abs_eq` splits that into `inner ℝ u v = 1` or `= -1`;
   substituting each into step 1 gives `v = u` or `v = -u`, contradicting
   `hne1` / `hne2` (`simp ... at h_eq ⊢ <;> tauto`).

**Used in.** `norm_normalized_orthProj` (to invert the norm) and throughout
`rankin_bound_general`, where excluding `±u` from the filtered set `T` is
exactly what makes the normalized projections well defined.

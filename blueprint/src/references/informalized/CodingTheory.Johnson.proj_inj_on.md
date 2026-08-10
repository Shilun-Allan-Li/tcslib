<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: proj_inj_on -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Projection off `u` is injective on unit vectors obtuse to `u`

**Claim.** Let `u : V` be a unit vector in a real inner product space and
`S : Set V` a set of unit vectors (`hS_norm`) each with `inner ℝ x u ≤ 0`
(`hS_inner`). Then `Set.InjOn (fun x => x - (inner ℝ x u) • u) S`.

**Proof.** Take `x y ∈ S` with equal projections and set
`c := inner ℝ x u - inner ℝ y u`.

1. Subtracting the two projection equations gives `x - y = c • u`
   (`sub_smul`, `sub_eq_zero`).
2. Expanding `‖x - y‖^2` two ways: `norm_sub_sq ℝ` with `‖x‖ = ‖y‖ = 1` gives
   `2 - 2 * ⟪x, y⟫`, while step 1 with `norm_smul` and `‖u‖ = 1` gives `c^2`.
3. From `x = y + c • u` and `norm_add_sq ℝ`, `‖x‖^2 = 1 + 2*c*⟪y, u⟫ + c^2`;
   comparing with `‖x‖ = 1` forces `c * (c + 2 * ⟪y, u⟫) = 0`, so
   `c = 0 ∨ c = -2 * ⟪y, u⟫` (`Classical.or_iff_not_imp_left`,
   `mul_left_cancel₀`, `nlinarith`).
4. `grind` closes both cases: `c = 0` gives `x = y` directly by step 1, and in
   the other case the same two evaluations of `‖x - y‖^2` collapse to `x = y`.

**Remark.** This is the set-level ancestor of `normalized_orthProj_injective`;
the Rankin bound uses the latter (a `False`-valued clash form on the normalized
projections) rather than this one.

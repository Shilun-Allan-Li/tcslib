<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: orthProj_mem_orthogonal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `orthProj u v` lands in the orthogonal complement of `span {u}`

**Claim.** For `u v : V` in a real inner product space with `‖u‖ = 1`,
`orthProj u v = v - (inner ℝ u v) • u` belongs to `(Submodule.span ℝ {u})ᗮ`.

**Proof.** Membership in `ᗮ` unfolds to: every `x ∈ Submodule.span ℝ {u}` is
orthogonal to `orthProj u v` (`intro x hx`).

1. `Submodule.mem_span_singleton.mp hx` writes `x = k • u` for some `k : ℝ`
   (`obtain ⟨k, rfl⟩`).
2. `simp [inner_sub_right, inner_smul_left, inner_smul_right]` expands
   `⟪k • u, v - ⟪u,v⟫ • u⟫` to `k * (⟪u,v⟫ - ⟪u,v⟫ * ⟪u,u⟫)`.
3. `rw [real_inner_self_eq_norm_sq, hu]` replaces `⟪u,u⟫` by `1`, and `ring`
   finishes: the bracket is `0`.

**Used in.** `mkProj`, which packages `‖orthProj u v‖⁻¹ • orthProj u v` as an
element of the subtype `(Submodule.span ℝ {u})ᗮ` (via `Submodule.smul_mem`) so
that `rankin_bound_general` can recurse into a space of one lower dimension.

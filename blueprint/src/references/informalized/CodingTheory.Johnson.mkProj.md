<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: mkProj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `mkProj`: normalized projection, bundled into the orthogonal complement

**Definition.** For a real inner product space `V`, a unit vector `u`
(`hu : ‖u‖ = 1`) and any `v : V`, the private definition `mkProj u hu v` is the
element of the subtype `↥(Submodule.span ℝ {u})ᗮ` whose underlying vector is
`‖orthProj u v‖⁻¹ • orthProj u v`, i.e. the normalized part of `v` orthogonal to
`u` (recall `orthProj u v = v - ⟪u, v⟫ • u`).

The membership certificate is `Submodule.smul_mem _ _ (orthProj_mem_orthogonal u v hu)`:
`orthProj u v` lies in `(span ℝ {u})ᗮ` and that subspace is closed under scalar
multiplication. `mkProj_val` records the projection-out equation
`((mkProj u hu v : _) : V) = ‖orthProj u v‖⁻¹ • orthProj u v` by `rfl`.

**Remark.** The point of the bundling is dimension bookkeeping, not new
mathematics: it makes the image `T.image (mkProj u hu)` a `Finset` of the
codimension-one subspace, so the induction hypothesis of `rankin_bound_general`
(stated for an arbitrary finite-dimensional space) can be applied there with
`finrank = d`. Note that no `v ≠ ±u` hypothesis is required — if
`orthProj u v = 0` then `‖0‖⁻¹ = 0` and the value is simply `0`; unit-ness and
injectivity of the map are supplied later by `norm_normalized_orthProj` and
`normalized_orthProj_injective` on the filtered set `T`.

**Used in.** `rankin_bound_general` (as the local `f`), which is specialised to
`Euc n` by `rankin_finset_bound`.

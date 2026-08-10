<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: mkProj_val -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Underlying vector of `mkProj`

**Claim.** For `u v : V` in a real inner product space with `hu : ‖u‖ = 1`,
the underlying vector of `mkProj u hu v` is
`‖orthProj u v‖⁻¹ • orthProj u v`. Here `mkProj` is the `private` packaging of
the normalized projection as an element of the subtype
`(Submodule.span ℝ {u})ᗮ`, its membership certificate being
`Submodule.smul_mem _ _ (orthProj_mem_orthogonal u v hu)`.

**Proof.** `rfl` — the coercion of a `Subtype.mk` is its first component, so
the statement holds definitionally.

**Remark.** A `private` projection-unfolding lemma, not a mathematical step:
`rankin_bound_general` uses it (as `rw [mkProj_val]` / `simp only [f, mkProj_val]`)
to get from the packaged subtype element back to the plain vector, where
`norm_normalized_orthProj` and `normalized_orthProj_inner_nonpos` apply.

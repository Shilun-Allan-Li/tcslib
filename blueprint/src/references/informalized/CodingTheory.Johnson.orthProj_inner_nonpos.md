<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: orthProj_inner_nonpos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Projection off `u` preserves non-positive inner products

**Claim.** Let `u v w : V` in a real inner product space with `‖u‖ = 1` and
`inner ℝ v w ≤ 0`, `inner ℝ v u ≤ 0`, `inner ℝ w u ≤ 0`. Then
`inner ℝ (orthProj u v) (orthProj u w) ≤ 0`.

**Proof.**

1. `huu : ⟪u, u⟫_ℝ = 1` from `real_inner_self_eq_norm_sq` and `hu`.
2. `unfold orthProj` and expand bilinearly with `simp [inner_sub_left,
   inner_sub_right, inner_smul_left, inner_smul_right]`, then `ring_nf`; using
   step 1 the inner product becomes `⟪v,w⟫ - ⟪u,v⟫ * ⟪u,w⟫`.
3. `nlinarith [real_inner_comm u w, real_inner_comm v u, huu]`: symmetry turns
   the two hypotheses into `⟪u,v⟫ ≤ 0` and `⟪u,w⟫ ≤ 0`, so their product is
   `≥ 0`, and subtracting it from `⟪v,w⟫ ≤ 0` stays `≤ 0`.

**Used in.** `normalized_orthProj_inner_nonpos`, which rescales both arguments
by non-negative factors; that is the "pairwise obtuse" hypothesis fed to the
inductive call in `rankin_bound_general`.

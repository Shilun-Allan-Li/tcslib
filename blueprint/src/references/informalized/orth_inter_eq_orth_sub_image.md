<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: orth_inter_eq_orth_sub_image -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The orthogonal intersection as an intrinsic complement inside V_M

**Claim.** For `M : Finset (Fin n)` and `S : Submodule (F p) (V n p)`,
`sym_orth S ⊓ V_sub M` equals the image under `(V_sub M).subtype` of
`(sym_form_sub M).orthogonal (S.map (r_E M))`. Here `sym_form_sub M` is the
symplectic form restricted to the subspace `V_sub M`, and `S.map (r_E M)` is the
image of `S` under restriction, viewed as a submodule of `V_sub M`. In words:
the ambient intersection is the *intrinsic* orthogonal complement, computed
inside `V_sub M`, of the restricted code.

**Proof.**

1. `convert orth_inter_eq_orth_map M S using 1` reduces the goal to identifying
   the two descriptions of the same set — the ambient complement of
   `S.map (r_E_V M)` intersected with `V_sub M`, versus the pushforward of the
   intrinsic complement of `S.map (r_E M)`.
2. `ext` plus `simp [sym_form_sub]` unfolds the restricted form to the ambient
   `symB` composed with the inclusion, and `simp [symB, IsOrtho]` reduces both
   orthogonality conditions to the same equation `sym_form _ v = 0`.
3. `simp [r_E_V, Subtype.ext_iff]` identifies the two images: `r_E_V M` is
   literally `(V_sub M).subtype ∘ₗ r_E M`, so mapping by it is mapping by `r_E M`
   and then including. `grind` closes the residual bookkeeping.

**Remark.** This is the step that makes the dimension count available: Mathlib's
`LinearMap.BilinForm.finrank_orthogonal` needs a complement taken with respect
to a nondegenerate form on the ambient space, and `sym_form_sub M` is
nondegenerate on `V_sub M` even though it is a restriction.

**Used in.** `dim_orth_inter`, giving
`finrank (sym_orth S ⊓ V_sub M) = 2 * M.card − finrank (S.map (r_E M))`.

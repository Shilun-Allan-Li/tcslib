<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: dim_orth_inter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Dimension of the symplectic dual intersected with a support subspace

**Claim.** For `M : Finset (Fin n)` and `S ≤ V n p`,
`finrank (sym_orth S ⊓ V_sub M) = 2 * M.card - finrank (S.map (r_E M))`.

**Proof.** Push the computation into the symplectic space `V_sub M`, where the
restricted form is nondegenerate.

1. `orth_inter_eq_orth_sub_image` gives
   `sym_orth S ⊓ V_sub M = ((sym_form_sub M).orthogonal (S.map (r_E M))).map (V_sub M).subtype`
   — computing the dual of `S` and then cutting down to `M` is the same as
   computing the dual of the restricted code inside `V_sub M`.
2. Inside `V_sub M`, `LinearMap.BilinForm.finrank_orthogonal` gives
   `finrank (orthogonal W) = finrank (V_sub M) - finrank W` for every `W`,
   using `sym_form_sub_isRefl` and `sym_form_sub_nondegenerate`.
3. Instantiate at `W := S.map (r_E M)`; the `map … subtype` in step 1 does not
   change finrank (`Submodule.finrank_map_subtype_eq`).
4. `dim_V_sub` replaces `finrank (V_sub M)` by `2 * M.card`.

**Used in.** `g_expansion` and `g_add_dims`, where together with `dim_map_r_E`
it expands `g S M = finrank (S_perp_M S M) - finrank (S_M S M)` into pure
dimension counts.

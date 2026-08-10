<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: orth_inter_eq_orth_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Inside V_M, only the restriction of S matters

**Claim.** For `M : Finset (Fin n)` and `S : Submodule (F p) (V n p)`,
`sym_orth S ⊓ V_sub M = sym_orth (S.map (r_E_V M)) ⊓ V_sub M`, where
`r_E_V M = (V_sub M).subtype ∘ₗ r_E M` is the restriction map viewed as an
endomorphism of `V n p`. So a vector supported in `M` is orthogonal to all of
`S` iff it is orthogonal to the restricted image `r_E_V M '' S`.

**Proof.** `ext v` and prove both inclusions; the engine both ways is
`sym_form_left_restrict M s v hvM : sym_form (r_E_V M s) v = sym_form s v`,
valid because `v ∈ V_sub M` kills every term of the sum outside `M`.

1. (⊆) Given `hvS : v ∈ sym_orth S` and `hvM : v ∈ V_sub M`, an element of
   `S.map (r_E_V M)` is `r_E_V M s` for some `s ∈ S` (`rintro _ ⟨s, hs, rfl⟩`).
   Then `sym_form s v = 0` from `hvS s hs`, and the displayed identity transports
   it to `sym_form (r_E_V M s) v = 0`, i.e. orthogonality
   (`LinearMap.BilinForm.IsOrtho`, `symB_apply`).
2. (⊇) Conversely, for `s ∈ S` apply the hypothesis to
   `r_E_V M s ∈ S.map (r_E_V M)` (`Submodule.mem_map_of_mem`) to get
   `sym_form (r_E_V M s) v = 0`, then rewrite back along the same identity to get
   `sym_form s v = 0`.

**Used in.** `orth_inter_eq_orth_sub_image`, which re-expresses the right-hand
side intrinsically inside `V_sub M`, en route to `dim_orth_inter`.

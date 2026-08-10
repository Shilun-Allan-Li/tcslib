<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: sym_form_left_restrict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Restricting the left argument does not change the pairing

**Claim.** For `M : Finset (Fin n)` and `s v : V n p` with `v ∈ V_sub M`,
`sym_form (r_E_V M s) v = sym_form s v`, where `r_E_V M` is the restriction
`r_E M` post-composed with `(V_sub M).subtype`, i.e. an endomorphism of
`V n p` that zeroes out the coordinates outside `M`.

**Proof.** Direct coordinate computation, not routed through antisymmetry.

1. `unfold r_E_V`, then `unfold sym_form r_E`: both sides become sums over
   `Finset.univ`, and `Finset.sum_congr rfl` reduces the goal to one index `i`.
2. `by_cases hiM : i ∈ M`. For `i ∈ M`, the `if i ∈ M` guard in `r_E` selects
   `s.1 i` / `s.2 i` unchanged, so the summands coincide (`simp [hiM]`).
3. For `i ∉ M`, `hv i hiM` gives `v.1 i = 0` and `v.2 i = 0`, so both summands
   vanish (`simp [hiM, hv0.1, hv0.2]`).

**Used in.** `orth_inter_eq_orth_map`, in both inclusions — it is what lets
`S^⊥ω ⊓ V_M` be recomputed from the restricted subspace `r_M(S)`. (Note that
`sym_form_r_E_left` states the identical fact but is unused.)

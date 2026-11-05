<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: sym_form_sub_nondegenerate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The restricted symplectic form is non-degenerate

**Claim.** For every `M : Finset (Fin n)`, the form `sym_form_sub M` on the
subspace `V_sub M` is non-degenerate: if `sym_form_sub M v w = 0` for all
`w : ↥(V_sub M)`, then `v = 0`.

**Proof.**
1. `intro v hv`, then `Classical.byContradiction` with
   `hv_nonzero : ¬ (v = 0)`.
2. From the contrapositive of `sym_form_nondegenerate_on_V_sub M v.1 v.2`,
   `obtain ⟨w, hw⟩` a witness `w : V_sub M` with `sym_form v.1 w.1 ≠ 0`
   (`convert ... using 1`, then `simp +zetaDelta` and `grind` to match the
   negated form of that lemma).
3. But `hv w` says exactly that this pairing is `0`, so `exact hw (hv w)`
   closes the goal.

**Used in.** `dim_orth_inter`, as the `Nondegenerate` hypothesis of
`LinearMap.BilinForm.finrank_orthogonal` — this is what makes
`dim (S^⊥ω ⊓ V_M) = 2|M| - dim (r_M S)` available.

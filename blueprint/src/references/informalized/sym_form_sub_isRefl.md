<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: sym_form_sub_isRefl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The restricted symplectic form is reflexive

**Claim.** For every `M : Finset (Fin n)`, the form `sym_form_sub M` on the
subspace `V_sub M` is reflexive (`LinearMap.BilinForm.IsRefl`): if
`sym_form_sub M v w = 0` then `sym_form_sub M w v = 0`.

**Proof.**
1. `intro v w h`, then `simpa [sym_form_sub_apply] using h` pushes the
   hypothesis down to the ambient form: `sym_form ↑v ↑w = 0`.
2. A `calc` step uses antisymmetry `sym_form_swap ↑w ↑v` to get
   `sym_form ↑w ↑v = - sym_form ↑v ↑w`, which is `0` by step 1.
3. `simpa [sym_form_sub_apply] using hwv` lifts the conclusion back to the
   restricted form.

The same three-line pattern as `symB_isRefl`, one level down on the subspace.

**Used in.** `dim_orth_inter`, as the `IsRefl` hypothesis of
`LinearMap.BilinForm.finrank_orthogonal` (paired with
`sym_form_sub_nondegenerate`).

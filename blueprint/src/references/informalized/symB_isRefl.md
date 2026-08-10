<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: symB_isRefl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The symplectic bilinear form is reflexive

**Claim.** The standard symplectic form on `V n p = (Fin n → F p) × (Fin n → F p)`,
packaged as the bilinear form `symB`, is reflexive (`LinearMap.BilinForm.IsRefl`):
whenever `symB v w = 0` we also have `symB w v = 0`.

**Proof.**
1. `intro v w h`, then `simpa [symB_apply] using h` replaces the bilinear-form
   application by the underlying `sym_form v w = 0`.
2. Antisymmetry `sym_form_swap w v` gives `sym_form w v = - sym_form v w`, so
   `simpa [sym_form_swap, h']` yields `sym_form w v = 0`.
3. `simpa [symB_apply]` transports that back up to `symB w v = 0`.

Reflexivity here is genuinely a consequence of *anti*symmetry: the form is
alternating, but vanishing is preserved under negation, so the orthogonality
relation it induces is symmetric.

**Used in.** `finrank_sym_orth` — the `IsRefl` argument of
`LinearMap.BilinForm.finrank_orthogonal`, alongside `symB_nondegenerate`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: symB_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The bundled bilinear form evaluates to the symplectic form

**Claim.** For all `x y : V n p`, the bundled bilinear form `symB` applied to
`x` and `y` equals `sym_form x y`. Here `sym_form u v = ∑ i, u₁ᵢ v₂ᵢ − u₂ᵢ v₁ᵢ`
is the standard symplectic form on `V n p = (Fin n → F p) × (Fin n → F p)`, and
`symB` is that same form repackaged as a `LinearMap.BilinForm (F p) (V n p)` via
`LinearMap.mk₂`.

**Proof.** Immediate from `rfl` — `symB` is built by `LinearMap.mk₂` from the
function `fun x y => sym_form x y`, so its application is definitionally
`sym_form x y`. The bilinearity side conditions of `mk₂` (`sym_form_add_left`,
`sym_form_smul_left`, `sym_form_add_right`, `sym_form_smul_right`) are data of
the definition and play no part here.

**Used in.** This is a plumbing lemma, marked `@[simp]`, whose only job is to
let `simp`/`simpa` move between the unbundled `sym_form` and the bundled `symB`
that Mathlib's orthogonal-complement API (`LinearMap.BilinForm.orthogonal`,
used to define `sym_orth`) requires. It is discharged that way inside
`orth_inter_eq_orth_map`, `symB_nondegenerate`, and `symB_isRefl`.

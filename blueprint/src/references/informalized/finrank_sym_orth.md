<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: finrank_sym_orth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Dimension of the symplectic orthogonal complement

**Claim.** For any submodule `S : Submodule (F p) (V n p)`,
`finrank (sym_orth S) = 2 * n − finrank S`, where
`sym_orth S = (symB).orthogonal S` is the orthogonal complement with respect to
the standard symplectic form. No isotropy is assumed — this holds for every
subspace.

**Proof.**

1. Apply `LinearMap.BilinForm.finrank_orthogonal` to `B := symB`, supplying its
   two hypotheses: `symB_nondegenerate` (nondegeneracy, itself reduced to
   `sym_form_nondegenerate` via `symB_apply`) and `symB_isRefl` (reflexivity,
   from the antisymmetry `sym_form_swap`). This yields
   `finrank (symB.orthogonal S) = finrank (F p) (V n p) − finrank S`.
2. `simpa [sym_orth, finrank_V]` unfolds the abbreviation `sym_orth` and replaces
   the ambient dimension by `2 * n`.

**Remark.** Nondegeneracy is what makes the complement behave dimensionally like
a genuine perp; the form's antisymmetry (rather than symmetry) is harmless since
Mathlib only requires `IsRefl`.

**Used in.** `finrank_le_n_of_isotropic` — combining this with
`finrank S ≤ finrank (sym_orth S)` for isotropic `S` gives `finrank S ≤ n` — and
in the rigidity step where `S = sym_orth S` is forced when `finrank S = n`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumHamming.lean :: codeProj_eq_self_of_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The code projector fixes code vectors

**Claim.** If `x : Hn n` lies in the code `C : Submodule ℂ (Hn n)`, then
`codeProj C x = x`. Both `C` and `x` are implicit, so the lemma is applied by
supplying only the membership proof `hx : x ∈ C`.

**Proof.** Two steps.

1. `h_proj`: for every `x ∈ C`, `Submodule.orthogonalProjection C x = x` — this
   is `Submodule.starProjection_eq_self_iff.mpr hx`, Mathlib's characterisation
   of the fixed points of the orthogonal projection.
2. `apply h_proj; assumption` — the goal about `codeProj` matches after the
   coercion is unfolded, so the specialised statement closes it directly.

**Remark.** The only mathematical input is Mathlib's
`starProjection_eq_self_iff`; the surrounding `have` exists to state it in the
`orthogonalProjection` form that the goal presents.

**Used in.** `codeProj_idempotent`, and in `error_subspaces_orthogonal` (as the
rewrite `codeProj C y = y` for `y` in the code, which is what lets the
non-degeneracy hypothesis `Π_C ∘ E† ∘ F ∘ Π_C = 0` be applied to bare code
vectors).

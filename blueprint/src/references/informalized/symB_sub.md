<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: symB_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The symplectic form restricted to a support subspace

**Definition.** For `M : Finset (Fin n)`,

```
symB_sub M = (symB).comp (V_sub M).subtype (V_sub M).subtype
    : LinearMap.BilinForm (F p) (V_sub M)
```

the bundled symplectic form `symB` on `V n p` pulled back along the inclusion
`(V_sub M).subtype : V_sub M →ₗ V n p` in both arguments. So for
`x y : V_sub M` its value is `sym_form ↑x ↑y`, the ambient symplectic pairing of
the two underlying vectors — no new pairing is introduced, only a form living on
the subspace.

Bundling it this way is what makes Mathlib's bilinear-form API available on
`V_sub M`, in particular `LinearMap.BilinForm.orthogonal` and the
`Nondegenerate` / `IsRefl` predicates.

**Used in.** Immediately aliased as `sym_form_sub`; the defining equation is
`sym_form_sub_apply` (proved by `rfl`), and `sym_form_sub_nondegenerate`,
`sym_form_sub_isRefl`, `orth_inter_eq_orth_sub_image` and `dim_orth_inter` are
stated in terms of it.

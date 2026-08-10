<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: sym_form_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Notation for the restricted symplectic form

**Definition.** For `M : Finset (Fin n)`,

```
sym_form_sub M = symB_sub M : LinearMap.BilinForm (F p) ↥(V_sub M)
```

This is an `abbrev`, i.e. a reducible alias: `sym_form_sub M` *is*
`symB_sub M`, the ambient symplectic form `symB` pulled back along
`(V_sub M).subtype` in both arguments. It carries no content of its own — it
exists so that the subspace form can be written with the `sym_form` naming
convention used elsewhere in the file.

Its value is pinned down by the `@[simp]` lemma `sym_form_sub_apply`:
`sym_form_sub M x y = sym_form ↑x ↑y`, proved by `rfl`.

**Used in.** `sym_form_sub_nondegenerate`, `sym_form_sub_isRefl`,
`orth_inter_eq_orth_sub_image` (which identifies `sym_orth S ⊓ V_sub M` with the
image of `(sym_form_sub M).orthogonal (S.map (r_E M))`) and `dim_orth_inter`,
the rank computation behind `g_expansion`.

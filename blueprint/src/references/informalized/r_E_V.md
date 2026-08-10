<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: r_E_V -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Coordinate restriction as an endomorphism of `V`

**Definition.** For `E : Finset (Fin n)`,

```
r_E_V E = (V_sub E).subtype.comp (r_E E) : V n p →ₗ[F p] V n p
```

i.e. the restriction map `r_E E : V n p →ₗ V_sub E` (which zeroes every
coordinate outside `E`) followed by the inclusion `V_sub E ↪ V n p`. Concretely
`r_E_V E v` is `v` with all coordinates outside `E` set to `0`, but typed as a
vector of `V n p` rather than of the subspace.

The only point of the definition is that it is an endomorphism of the ambient
space, so it can be fed to `sym_form` on either side and to `Submodule.map`
without shuffling subtype coercions; unfolding it (`simp [r_E_V]`,
`unfold r_E_V`) recovers the `r_E` statements.

**Used in.** `sym_form_r_E_left` and `sym_form_left_restrict`
(`sym_form (r_E_V M s) v = sym_form s v` for `v ∈ V_sub M`), and through them
`orth_inter_eq_orth_map`, which rewrites `sym_orth S ⊓ V_sub M` as
`sym_orth (S.map (r_E_V M)) ⊓ V_sub M`.

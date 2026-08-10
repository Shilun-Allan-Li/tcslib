<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: S_perp_M -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The symplectic dual intersected with a support subspace

**Definition.** For a submodule `S` of `V n p = (Fin n → F p) × (Fin n → F p)`
and a coordinate set `M : Finset (Fin n)`,

```
S_perp_M S M = sym_orth S ⊓ V_sub M
```

as a submodule of `V n p`: the vectors that are symplectically orthogonal to all
of `S` (`sym_orth S = (symB).orthogonal S`) **and** supported inside `M` (all
coordinates outside `M` vanish, `V_sub M`). It is the companion of
`S_M S M = S ⊓ V_sub M`.

Nothing is proved here — the definition is a plain `⊓` of two existing
submodules, and `rfl` suffices to unfold it (as `g_expansion` does with
`show S_perp_M S M = sym_orth S ⊓ V_sub M from rfl`).

**Used in.** `g S M = finrank (S_perp_M S M) - finrank (S_M S M)`, the count of
logical operators supportable on `M`; from there `dim_orth_inter`,
`g_expansion`, `correctable_implies_g_zero` and `g_le_two_card_C` feed
`quantum_singleton_bound`.

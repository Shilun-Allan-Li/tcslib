<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: S_M -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `S_M S M`: the part of the code supported inside `M`

**Definition.** For a submodule `S ≤ V n p` and `M : Finset (Fin n)`,
`S_M S M := S ⊓ V_sub M` — the submodule of stabilizer elements all of whose
non-zero coordinates lie in `M`. As a `Submodule (F p) (V n p)` it is just the
meet of `S` with the support subspace `V_sub M`, so no proof obligation is
attached.

It is one of the two halves of the cleaning bookkeeping:

- `S_perp_M S M := sym_orth S ⊓ V_sub M`, the same construction for the
  symplectic orthogonal complement;
- `g S M := finrank (S_perp_M S M) - finrank (S_M S M)`, the count of logical
  operators supportable on `M`.

**Used in.** `g` (and hence every `g_*` lemma), `g_expansion`,
`dim_S_M_add_dim_S_M_c_le_dim_S`, `g_add_dims`, `dim_ineq_aux`,
`cleaning_dimension_identity`, `correctable_implies_g_zero` and
`g_le_two_card_C`. `dim_S_M_add_dim_S_M_c_le_dim_S` records the key property:
`dim (S_M S M) + dim (S_M S (E_c M)) ≤ dim S`.

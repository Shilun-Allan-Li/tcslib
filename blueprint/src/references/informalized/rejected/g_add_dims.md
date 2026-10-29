<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: g_add_dims -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Subtraction-free form of the g(M) identity

**Claim.** For isotropic `S` and `M : Finset (Fin n)`,
`g S M + finrank (S_M S M) + finrank S = 2 * M.card + finrank (S_M S (E_c M))`.
This is `g_formula` with every truncated subtraction cleared: an equation between
two sums of naturals, so it can be fed directly to `linarith`/`omega`.

**Proof.**

1. `have h_g_def := g_formula S hS M` and
   `have := dim_S_M_add_dim_S_M_c_le_dim_S S M`
   (the latter: `finrank (S_M S M) + finrank (S_M S (E_c M)) ≤ finrank S`).
2. `contrapose! h_g_def` — assume the additive equation fails and derive that
   `g_formula` fails too.
3. `rw [Ne.eq_def, eq_tsub_iff_add_eq_of_le]` turns the negated `x = a − b` into
   the additive statement; `cases lt_or_gt_of_ne h_g_def <;> linarith` closes the
   main branch from either strict inequality.
4. The `≤` side condition of `eq_tsub_iff_add_eq_of_le`, namely
   `finrank S + finrank (S_M S M) ≤ 2 * M.card + finrank (S_M S (E_c M))`, is
   assembled from `dim_orth_inter M S` and `dim_map_r_E S M` (after
   `unfold S_M` and `rw [eq_tsub_iff_add_eq_of_le] at *`), together with
   isotropy: `S ⊓ V_sub M ≤ sym_orth S ⊓ V_sub M` by
   `inf_le_inf_right (V_sub M) hS`, so `Submodule.finrank_mono` gives the
   comparison `linarith` needs. Its own side goals use
   `Submodule.finrank_le` with `dim_V_sub`, and `Nat.le_of_add_left_le`
   applied to the bound from step 1.

**Used in.** `dim_ineq_aux` (a one-line `linarith` consequence) and
`cleaning_dimension_identity`, applied to both `M` and `E_c M` — the two
ingredients of `quantum_singleton_bound`.

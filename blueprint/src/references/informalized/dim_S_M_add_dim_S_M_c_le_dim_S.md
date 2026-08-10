<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: dim_S_M_add_dim_S_M_c_le_dim_S -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Complementary restrictions of `S` have dimensions summing to at most `dim S`

**Claim.** For `S ≤ V n p` and `M : Finset (Fin n)`,
`finrank (S_M S M) + finrank (S_M S (E_c M)) ≤ finrank S`, where
`S_M S M = S ⊓ V_sub M` is the part of `S` supported inside `M`.

**Proof.** The two pieces are independent inside `S`.

1. Rewrite the left side with
   `Submodule.finrank_sup_add_finrank_inf_eq`, replacing
   `finrank A + finrank B` by `finrank (A ⊔ B) + finrank (A ⊓ B)`.
2. `S_M S M ⊔ S_M S (E_c M) ≤ S` since each summand is `≤ S`
   (`sup_le` on `inf_le_left`), so `Submodule.finrank_mono` bounds the join term
   by `finrank S` (`le_trans (add_le_add_right …)`).
3. It remains to show the intersection term is `0`, i.e.
   `S_M S M ⊓ S_M S (E_c M) = ⊥`: a vector supported in both `M` and `Mᶜ`
   vanishes at every coordinate (`simp [S_M]`, `simp [Submodule.eq_bot_iff, V_sub]`,
   `simp_all [E_c, funext_iff]`).
4. The final `exact` supplies the witness by cases on `i ∈ M`, taking the
   vanishing datum from the `Mᶜ`-hypothesis or the `M`-hypothesis accordingly.

**Used in.** `g_add_dims`, as the ℕ-subtraction side condition that lets the
`g`-formula be rearranged into an equality.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: g_expansion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Expansion of g(M) in terms of code dimensions

**Claim.** Let `S` be isotropic (`hS : IsIsotropic S`) and `M : Finset (Fin n)`.
Then
`g S M = 2 * M.card + finrank (S_M S (E_c M)) − finrank S − finrank (S_M S M)`,
where `g S M = finrank (S_perp_M S M) − finrank (S_M S M)` counts logical
operators supportable on `M`, `S_M S M = S ⊓ V_sub M`, and `E_c M = Mᶜ`. All
subtractions are truncated subtraction on `ℕ`.

**Proof.**

1. `unfold g` and rewrite `S_perp_M S M = sym_orth S ⊓ V_sub M` (`rfl`), then
   apply `dim_orth_inter` to get
   `g S M = 2 * M.card − finrank (S.map (r_E M)) − finrank (S_M S M)`.
2. `dim_map_r_E` gives
   `finrank (S.map (r_E M)) = finrank S − finrank (S_M S (E_c M))`
   (rank–nullity for `r_E M`, with `ker_r_E` identifying the kernel).
3. Substituting and rearranging is pure `ℕ`-subtraction bookkeeping:
   `tsub_tsub`, `tsub_add_eq_add_tsub`, `Nat.sub_eq_of_eq_add`, `add_comm`,
   `ring`, closed by `omega`.
4. The rearrangement in step 3 needs two `≤` side conditions, which is where
   isotropy enters:
   - `finrank (S.map (r_E M)) ≤ 2 * M.card`, since the image sits in `V_sub M`
     (`Submodule.finrank_le`) and `dim_V_sub` evaluates that to `2 * M.card`;
   - `finrank (S_M S M) ≤ 2 * M.card − finrank (S.map (r_E M))`, since
     `hS` gives `S_M S M ≤ S_perp_M S M` (`fun x hx => ⟨hS hx.1, hx.2⟩`), so
     `Submodule.finrank_mono` plus `dim_orth_inter` bounds it.

**Remark.** Isotropy is used *only* to keep the truncated subtractions honest;
the underlying identity is the rank–nullity count for restriction to `M`.

**Used in.** `g_formula` (same identity, regrouped), hence `g_add_dims` and the
cleaning-lemma chain behind `quantum_singleton_bound`.

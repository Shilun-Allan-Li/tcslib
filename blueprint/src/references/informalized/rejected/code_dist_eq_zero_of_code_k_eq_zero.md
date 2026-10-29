<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: code_dist_eq_zero_of_code_k_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# No logical qudits forces distance zero

**Claim.** Let `S` be an isotropic submodule of `V n p` (`IsIsotropic S`, i.e.
`S ≤ sym_orth S`) with `code_k S = 0`, where `code_k S = n - finrank S`. Then
`code_dist S = 0`.

**Proof.** The hypothesis pins the dimension, which forces `S` to be maximally
isotropic, and then the distance set is empty.

1. `finrank S ≤ n` by `finrank_le_n_of_isotropic`, and `code_k S = 0` unfolds to
   `n - finrank S = 0`, giving `n ≤ finrank S` (`Nat.sub_eq_zero_iff_le`); hence
   `finrank S = n` (`Nat.le_antisymm`).
2. `finrank (sym_orth S) = 2 * n - finrank S = 2 * n - n = n = finrank S`
   (`calc` on `finrank_sym_orth`).
3. From `S ≤ sym_orth S` and equal finranks, `S = sym_orth S`
   (`Submodule.eq_of_le_of_finrank_eq`).
4. Rewriting `sym_orth S` by `S` in `code_dist`, the index set becomes
   `{d | ∃ v ∈ S, v ∉ S ∧ wt v = d}`, which is empty: `rintro ⟨v, hvS, hvnotS, -⟩`
   gives the contradiction `hvnotS hvS`.
5. `sInf ∅ = 0` closes the goal (`simp`).

**Used in.** `quantum_singleton_bound`, to dispose of the `code_k S = 0` case,
where the bound would otherwise have nothing to spend on `2 * (d - 1)`.

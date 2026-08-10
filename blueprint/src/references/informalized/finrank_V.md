<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: finrank_V -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The symplectic space has dimension 2n

**Claim.** `Module.finrank (F p) (V n p) = 2 * n`, where
`V n p = (Fin n → F p) × (Fin n → F p)`. A granular bookkeeping lemma: it moves
the already-proved dimension count for support subspaces to the ambient space.

**Proof.**

1. Instantiate `dim_V_sub` at `C = Finset.univ` to get
   `finrank (V_sub (univ : Finset (Fin n))) = 2 * Finset.univ.card`, and
   `Finset.univ.card = n` for `Fin n` (`simp`).
2. `V_sub_univ_eq_top` states `V_sub univ = (⊤ : Submodule (F p) (V n p))`;
   rewriting with it turns step 1 into `finrank (⊤ : Submodule _ _) = 2 * n`.
3. `Submodule.finrank_top` identifies `finrank (⊤ : Submodule (F p) (V n p))`
   with `finrank (F p) (V n p)`.
4. Chain the two equalities: `exact ht.symm.trans h'`.

**Used in.** `finrank_sym_orth` (as the ambient dimension in the
orthogonal-complement count) and `finrank_le_n_of_isotropic`.

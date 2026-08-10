<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: V_sub_univ_eq_top -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The support subspace of all coordinates is everything

**Claim.** `V_sub (Finset.univ : Finset (Fin n)) = (⊤ : Submodule (F p) (V n p))`.
Here `V_sub C` is the subspace of `V n p = (Fin n → F p) × (Fin n → F p)` of
vectors whose coordinates vanish outside `C`; taking `C = univ` imposes no
condition. Tagged `@[simp]`.

**Proof.** `ext v` and prove both inclusions.

1. Forward: any `v` lies in `⊤` — `trivial`.
2. Backward: membership in `V_sub univ` unfolds to `∀ i ∉ univ, v.1 i = 0 ∧ v.2 i = 0`.
   The hypothesis `hi : i ∉ univ` contradicts `Finset.mem_univ i`, so the goal
   is closed by `False.elim`.

**Used in.** `finrank_V`, to turn the general dimension count
`dim_V_sub : finrank (V_sub C) = 2 * C.card` at `C = univ` into
`finrank (V n p) = 2 * n`.

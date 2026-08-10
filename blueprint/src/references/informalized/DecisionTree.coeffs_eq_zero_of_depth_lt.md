<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean :: coeffs_eq_zero_of_depth_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Frequencies larger than the depth carry no weight

**Claim.** For `T : DecisionTree n` and `S : Finset (Fin n)`, if
`T.depth < S.card` then `T.coeffs S = 0`.

**Proof.** `induction T generalizing S` — the frequency must be generalized
because the branch case applies the inductive hypotheses at two different
frequencies.

1. **Leaf `b`.** Here `T.depth = 0`, so `0 < S.card` and hence `S ≠ ∅` (the
   `have hS`, obtained by rewriting `S = ∅` into `h` and closing with
   `simp [DecisionTree.depth]`). Then `simp [coeffs, hS]` takes the `else`
   branch of the leaf clause.
2. **Branch `i lo hi`.** `simp only [DecisionTree.depth] at h` turns the
   hypothesis into `1 + max lo.depth hi.depth < S.card`, so both subtree depths
   are strictly below `S.card`. `have hSi := card_symmDiff_singleton S i` gives
   `S.card - 1 ≤ (S ∆ {i}).card`, which is exactly enough slack to also put
   both subtree depths strictly below `(S ∆ {i}).card`.
3. `rw [coeffs, ih_lo _ (by omega), ih_hi _ (by omega), ih_lo _ (by omega),
   ih_hi _ (by omega)]` zeroes all four terms of the branch clause — the two
   at `S` and the two at `S ∆ {i}` — and `ring` closes
   `(0 + 0)/2 + (0 − 0)/2 = 0`.

**Used in.** `degree_le_depth` (O'Donnell Proposition 3.16, degree bound): after
`fourierCoeff_signEval` rewrites the coefficient, a `by_contra`/`push_neg` on
the cardinality bound produces exactly this lemma's hypothesis.

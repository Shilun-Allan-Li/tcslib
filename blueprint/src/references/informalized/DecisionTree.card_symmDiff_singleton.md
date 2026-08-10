<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean :: card_symmDiff_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Toggling one coordinate drops the cardinality by at most one

**Claim.** For `S : Finset (Fin n)` and `i : Fin n`,
`S.card - 1 ≤ (S ∆ {i}).card`, with `-` the truncated subtraction on `ℕ`.

**Proof.** `by_cases h : i ∈ S`.

1. If `i ∈ S`, then `S ∆ {i} = S.erase i` — proved by `ext j` and
   `by_cases hj : j = i`, each branch closed by
   `simp [Finset.mem_symmDiff, Finset.mem_erase, hj, h]`. Rewriting and
   applying `Finset.card_erase_of_mem h` makes the goal
   `S.card - 1 ≤ S.card - 1`.
2. If `i ∉ S`, then `S ∆ {i} = insert i S` by the same `ext`/`by_cases`
   argument with `Finset.mem_insert`. Then
   `Finset.card_insert_of_notMem h` gives cardinality `S.card + 1`, and
   `omega` finishes.

A `private` arithmetic helper; the inequality is deliberately loose (one case is
an equality, the other slack by two) because only the bound is needed.

**Used in.** The branch case of `coeffs_eq_zero_of_depth_lt`, where it lets the
depth hypothesis `T.depth < S.card` be transported to the shifted frequency
`S ∆ {i}` before the four inductive-hypothesis applications.

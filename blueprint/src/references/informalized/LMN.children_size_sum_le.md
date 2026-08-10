<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RecursiveReduction.lean :: children_size_sum_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The children of a size-`s` node have total size at most `s − 1`

**Claim.** If `(Circuit.node isAnd cs).size ≤ s`, then
`cs.foldr (fun c acc => c.size + acc) 0 ≤ s - 1`.

**Proof.** One line: `exact Nat.le_sub_one_of_lt (lt_of_lt_of_le _ hs)`.

1. The inner `by cases cs <;> simp +decide [Circuit.size]` proves the strict
   inequality `cs.foldr (fun c acc => c.size + acc) 0 < (Circuit.node isAnd cs).size`,
   since by definition `(Circuit.node isAnd cs).size = 1 + cs.foldr …` — the `+1`
   accounts for the gate itself, and holds for both the empty and non-empty list.
2. `lt_of_lt_of_le` chains that with `hs` to get `fold < s`.
3. `Nat.le_sub_one_of_lt` converts `fold < s` to `fold ≤ s - 1`.

**Used in.** `child_size_le_parent` (same file) and the size bookkeeping in
`circuit_layer_reduction`
(`TCSlib/BooleanAnalysis/LMN/CircuitLayerReduction.lean`).

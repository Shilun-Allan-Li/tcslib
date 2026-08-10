<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RecursiveReduction.lean :: child_size_le_parent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A single child of a size-`s` node has size at most `s − 1`

**Claim.** Let `cs : List (Circuit n)`, `c ∈ cs`, and suppose
`(Circuit.node isAnd cs).size ≤ s`. Then `c.size ≤ s - 1`.

**Proof.**

1. `have h_c_in_cs : c.size ≤ cs.foldr (fun c acc => c.size + acc) 0` — a single
   child's size is at most the total over the list, since every summand is a
   natural number. Proved by `induction cs <;> simp_all +arith +decide`, then
   `cases hc <;> simp_all +arith +decide [Circuit.size]` to split `c ∈ cs` into
   head and tail, closed by `grind`.
2. `exact h_c_in_cs.trans (children_size_sum_le isAnd cs hs)` — chain with the
   total-size bound `s - 1`.

**Remark.** Strictly weaker than `children_size_sum_le`, which it is derived from;
the per-child form is the convenient one for a recursive call.

**Note.** Currently unused: no other declaration in the repository references
`child_size_le_parent` (the blueprint `\uses` list for
`CircuitLayerReduction.tex` mentions it, but the Lean proof there does not).

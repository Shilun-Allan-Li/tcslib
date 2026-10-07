<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: processClauseLits_aux_idx_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Aux indices stay below the clause length

**Claim.** Let `t : Term n` and suppose every pair of `lits` occurs in
`t.zipIdx` (`hmem`). Then every entry `e` of the aux output
`(processClauseLits lits path ρ₀ σ).2.2.2` satisfies `e.1 < t.length`.

**Proof.** Three steps, no induction here.

1. `processClauseLits_aux_entries_from_lits` (from `Switching/EncodingProperties.lean`)
   produces a literal pair `li ∈ lits` with `e.1 = li.2`: aux entries only ever
   record indices that came from the literal list.
2. `hmem li hli` puts `li` in `t.zipIdx`, and `List.mem_zipIdx` yields
   `li.2 < t.length` — indices produced by `zipIdx` are positions in `t`.
3. `rw [hidx]; omega`.

**Used in.** `encode_go_wellformed`: this is the side condition
`hpcl_idx_lt` that lets the clause's aux block be cast into
`List (Fin w × Bool)` via `toFinBlock`, after `lt_of_lt_of_le` with the width
bound `t.length ≤ w`.

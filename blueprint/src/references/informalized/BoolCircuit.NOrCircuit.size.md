<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: NOrCircuit.size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Node count of a normal-form OR-circuit

**Definition.** `NOrCircuit.size c : Nat`, defined in a `mutual` block with
`NAndCircuit.size`:

- `.clause _ _ ↦ 1` — a base clause is one node, whatever its literals.
- `.node cs ↦ 1 + cs.foldr (fun c acc => c.size + acc) 0` — one for the gate
  plus the total size of its `NAndCircuit` children.

A plain definition; no proof. The `Nodup` field of `.clause` is ignored.

**Remark.** The clause case is where this differs from `Circuit.size`, which
charges `1` per literal leaf plus `1` for the enclosing gate; the two measures
therefore disagree on clauses by a factor tracked separately by
`NOrCircuit.litCount`. This is exactly why the normalization bound is stated
with slack rather than as an equality.

**Used in.** `toNAnd_toNOr_size_le` (`(c.toNAnd).size ≤ 2 * c.size ∧
(c.toNOr).size ≤ 2 * c.size`), proved by `Circuit.ind` simultaneously for both
gate types, and its projections `toNAnd_size_le` / `toNOr_size_le`. Both the
base case (`simp +arith +decide [NOrCircuit.size, Circuit.size]`) and the
`.node` case unfold this definition directly.

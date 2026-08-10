<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: NAndCircuit.size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Size of an AND-rooted normal-form circuit

**Definition.** `NAndCircuit.size : NAndCircuit n → Nat`, defined in a `mutual`
block with `NOrCircuit.size`, counts nodes:

- `.clause _ _ => 1` — a whole clause is a single node, *regardless of how many
  literals it contains*;
- `.node cs => 1 + cs.foldr (fun c acc => c.size + acc) 0` — one for the gate
  plus the sizes of its `NOrCircuit` children.

Both the literal list and its `Nodup` proof are discarded in the `clause` case,
so `size` is a gate count, not a literal count. The measure that does count
literals is `NAndCircuit.litCount`, whose `clause` case is `lits.length`;
`NAndCircuit.depth` is the analogous `1 + foldr max 0` recursion.

This convention is what makes the normalization bound cheap: collapsing a chain
of same-kind gates into one clause costs one node no matter how wide it is.

**Used in.** `toNAnd_toNOr_size_le` and its projections `toNAnd_size_le`,
`toNOr_size_le`, which bound the normal form's size by `2 * c.size` for the
original `Circuit n`.

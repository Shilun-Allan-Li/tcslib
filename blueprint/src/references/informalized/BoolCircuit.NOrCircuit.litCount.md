<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: NOrCircuit.litCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Literal count of a normal-form OR-circuit

**Definition.** `NOrCircuit.litCount : NOrCircuit n → Nat` counts literal
occurrences:

```
(NOrCircuit.clause lits h).litCount = lits.length
(NOrCircuit.node cs).litCount       = cs.foldr (fun c acc => c.litCount + acc) 0
```

A base clause contributes its number of literals; an OR-node contributes the sum
over its `NAndCircuit` children. It is declared in a `mutual` block with
`NAndCircuit.litCount`, which has the same two equations on the AND side.

**Used in.** The normalization-preservation results: `toNAnd_toNOr_litCount`
proves `(c.toNAnd).litCount = c.litCount ∧ (c.toNOr).litCount = c.litCount` for
every general `Circuit`, with `toNOr_litCount` as the projected corollary — i.e.
converting a circuit to alternating normal form neither creates nor destroys
literals, in contrast to `NOrCircuit.size`, which is only bounded by `2 * c.size`
(`toNOr_size_le`).

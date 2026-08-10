<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: NAndCircuit.litCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Literal count of a normal-form AND-circuit

**Definition.** `NAndCircuit.litCount c : Nat` counts literal occurrences in an
AND-rooted normal-form circuit, mutually recursively with
`NOrCircuit.litCount`:

- `.clause lits _ ↦ lits.length` — a base clause contributes its number of
  literals (the `Nodup` proof is discarded).
- `.node cs ↦ cs.foldr (fun c acc => c.litCount + acc) 0` — a gate contributes
  the sum over its `NOrCircuit` children.

**Remark.** Because clauses are the leaves here, the recursion bottoms out one
level earlier than for `Circuit.litCount`, yet the totals agree: literals are
neither duplicated nor dropped by normalization.

**Used in.** `toNAnd_toNOr_litCount` and `toNAnd_litCount`, i.e.
`(c.toNAnd).litCount = c.litCount`; the fold-level step is the helper
`foldr_add_map`.

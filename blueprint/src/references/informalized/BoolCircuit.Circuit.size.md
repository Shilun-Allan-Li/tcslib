<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: Circuit.size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Size of a circuit: total node count

**Definition.** `Circuit.size : Circuit n → Nat` counts all nodes of the tree,
internal gates and literal leaves alike:

- `.lit _ => 1`;
- `.node _ cs => 1 + cs.foldr (fun c acc => c.size + acc) 0`, i.e. one for the
  gate itself plus the sum of the children's sizes.

The gate kind (`isAnd`) is ignored. Being a tree count, repeated subcircuits are
counted once per occurrence, so this is *formula* size rather than DAG size.

Two neighbouring definitions exist purely so the `foldr` bodies can be named in
proofs: `Circuit.sumSize cs = cs.foldr (fun c acc => c.size + acc) 0` (the
summand above) and `Circuit.maxDepth`, the analogous helper for
`Circuit.depth`. `Circuit.litCount` is the variant that counts only leaves.

**Used in.** The size-blowup bounds for normalization,
`toNAnd_toNOr_size_le` and its projections `toNAnd_size_le` /
`toNOr_size_le`, which state `(c.toNOr).size ≤ 2 * c.size` and the AND-side
mirror — the quantitative content of converting an unconstrained circuit into
the alternating `NAndCircuit` / `NOrCircuit` normal form.

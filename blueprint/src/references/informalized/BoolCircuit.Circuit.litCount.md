<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: Circuit.litCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Literal occurrences in a general circuit

**Definition.** `Circuit.litCount c : Nat` counts the literal leaves of a
`Circuit n` tree, by structural recursion: a leaf `.lit _` has count `1`, and a
gate `.node _ cs` has count `cs.foldr (fun c acc => c.litCount + acc) 0`, the
sum of its children's counts.

**Remark.** The gate flag `isAnd` is ignored (`.node _ cs`), so AND and OR
gates contribute nothing themselves — this is a count of *occurrences*, not of
distinct variables, so a literal repeated in several branches is counted once
per occurrence. An empty gate has count `0`.

**Used in.** `toNAnd_toNOr_litCount` (and its projections `toNAnd_litCount`,
`toNOr_litCount`), which show that normalization to `NAndCircuit` /
`NOrCircuit` preserves the literal count exactly — in contrast with
`Circuit.size`, which normalization can only bound by `2 * c.size`.

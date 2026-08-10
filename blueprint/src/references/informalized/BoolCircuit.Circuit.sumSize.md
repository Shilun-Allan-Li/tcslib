<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: Circuit.sumSize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Total size over a list of circuits

**Definition.** For `cs : List (Circuit n)`, `Circuit.sumSize cs : Nat` is
`cs.foldr (fun c acc => c.size + acc) 0`, the sum of the node counts
`Circuit.size c` over all `c ∈ cs`; the empty list gives `0`.

**Remark.** As with `Circuit.maxDepth`, this names the fold occurring in the
`.node` branch of `Circuit.size` (`1 + cs.foldr (fun c acc => c.size + acc)
0`), so `(Circuit.node b cs).size = 1 + Circuit.sumSize cs` by `rfl` — the `1`
accounting for the gate itself. Note the argument order of the accumulator
(`c.size + acc`) differs from the one used in the `toNAnd`/`toNOr` size bounds
(`acc + c.size`), which is why `foldr_add_map_le` is stated abstractly in `f`,
`g`, `h`.

**Note.** Also unreferenced: `Circuit.size` inlines the fold instead of calling
this definition, and no other file mentions `Circuit.sumSize`.

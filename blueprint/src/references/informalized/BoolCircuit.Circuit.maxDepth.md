<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: Circuit.maxDepth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Maximum depth over a list of circuits

**Definition.** For `cs : List (Circuit n)`, `Circuit.maxDepth cs : Nat` is
`cs.foldr (fun c acc => max c.depth acc) 0`, i.e. the largest `Circuit.depth`
among the members of `cs`, with the empty list giving `0`.

**Remark.** This is a named abbreviation for exactly the fold that appears
inside the `.node` branch of `Circuit.depth` (`1 + cs.foldr (fun c acc => max
c.depth acc) 0`), so `(Circuit.node b cs).depth = 1 + Circuit.maxDepth cs`
holds by `rfl` — but `Circuit.depth` writes the fold out rather than calling
this definition, so the two are only definitionally, not syntactically, linked.

**Note.** Despite the docstring ("used in depth of a node"), the declaration is
not referenced anywhere in the library; it is available API only.

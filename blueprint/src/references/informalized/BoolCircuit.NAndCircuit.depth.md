<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: NAndCircuit.depth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Depth of a normal-form AND-circuit

**Definition.** `NAndCircuit.depth c : Nat`, defined mutually with
`NOrCircuit.depth`:

- `.clause _ _ ↦ 0` — a base clause is a single level and counts as depth `0`.
- `.node cs ↦ 1 + cs.foldr (fun c acc => max c.depth acc) 0` — one for the gate
  plus the maximum depth of its `NOrCircuit` children.

**Remark.** This is *not* the same numbering as `Circuit.depth`: there a clause
appears as an explicit gate over literal leaves and so has depth `1`, whereas
here the whole clause is free. Since the normal form alternates, `depth` counts
alternations above the clause level.

**Note.** The declaration is not referenced anywhere else in the library — no
theorem in `Switching/Circuit.lean` relates it to `Circuit.depth`, unlike the
`litCount` and `size` measures. It is API provided for completeness alongside
`NOrCircuit.depth`.

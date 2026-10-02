<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: markLast_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# markLast preserves length

**Claim.** For every block `block : List (Fin w × Bool)`,
`(markLast block).length = block.length`. Attaching the "is-last" boolean flag to
each entry changes no lengths.

**Proof.** Structural recursion following `markLast`'s own three-case definition.

1. `[]`: both sides are `0` — `rfl`.
2. `[_]`: `markLast [hd] = [(hd.1, hd.2, true)]`, both sides `1` — `rfl`.
3. `hd :: hd2 :: rest`: `markLast` emits `(hd.1, hd.2, false) :: markLast (hd2 ::
   rest)`; the recursive call `markLast_length (hd2 :: rest)` gives the tail
   equality and `simp [ih]` adds one to each side.

**Used in.** The Razborov encoder's aux-length accounting (line 357,
`rw [markLast_length]`), where the number of emitted triples must match the number
of path steps in a clause block.

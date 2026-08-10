<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: markLast_getLast_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The last entry produced by markLast carries flag true

**Claim.** For every `block : List (Fin w × Bool)` and every proof
`hne : markLast block ≠ []`, the final triple satisfies
`((markLast block).getLast hne).2.2 = true`. So `markLast` flags exactly the last
entry of a block, which is what lets the decoder recognise clause boundaries.

**Proof.** Structural recursion mirroring `markLast`.

1. `[]`: then `markLast [] = []`, so `simp [markLast] at hne` closes the goal by
   contradiction.
2. `[hd]`: the list is `[(hd.1, hd.2, true)]` and its `getLast` is that triple —
   `rfl`.
3. `hd :: hd2 :: rest`: the tail is nonempty by `markLast_ne_nil _
   (List.cons_ne_nil _ _)`, so `List.getLast_cons hne'` rewrites the `getLast` of
   the cons to the `getLast` of `markLast (hd2 :: rest)`, and the recursive call
   `markLast_getLast_true (hd2 :: rest) hne'` finishes.

**Used in.** Line 368 of the encoder, combined with `markLast_ne_nil`, to show each
emitted clause block ends in a marked triple.

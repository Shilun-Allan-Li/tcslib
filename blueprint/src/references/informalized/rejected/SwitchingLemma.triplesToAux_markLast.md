<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: triplesToAux_markLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Serialising a marked block appends a termination marker

**Claim.** For `w : ℕ` and a nonempty `block : List (Fin w × Bool)`,
`triplesToAux w (markLast block) = block.map (fun p => (p.1.val, p.2)) ++ [(w, false)]`.
`markLast` sets the `hasMarker` flag on the last entry of `block` and clears it
on all others, so serialising the result reproduces the block's raw
`(index, direction)` entries followed by the single marker `(w, false)`.

**Proof.** `induction block`.

1. `nil`: impossible — `exact absurd rfl hne`.
2. Singleton `[(p, d)]`: `markLast` yields `[(p, d, true)]`, and
   `simp [markLast, triplesToAux]` produces `(p.val, d) :: (w, false) :: []`.
3. `(p, d) :: hd2 :: rest2`: a `have hML … := rfl` states the `markLast`
   unfolding for a two-or-more-element list, a second `rw [show … from rfl]`
   unfolds `triplesToAux` on the resulting `hasMarker = false` head, then
   `rw [ih (List.cons_ne_nil _ _)]` applies the induction hypothesis to the
   still-nonempty tail and `simp` reassociates the append.

**Used in.** `encode_go_wellformed` (private, same file): this is the step that
identifies one loop iteration's emitted aux block, together with its terminator,
with `triplesToAux` of a triple list.

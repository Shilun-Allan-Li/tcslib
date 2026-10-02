<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: triplesToAux -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Serializing marked `Fin w` triples into a flat index/direction list

**Definition.** For a width bound `w`, `triplesToAux w` is the recursive map
`List (Fin w × Bool × Bool) → List (ℕ × Bool)` that flattens each triple
`(pos, dir, hasMarker)` into `(pos.val, dir)`, and — when `hasMarker = true` —
emits an extra out-of-range sentinel entry `(w, false)` immediately after it.
The empty list maps to the empty list. So the third Boolean of each triple is
encoded positionally, as the presence of a `(w, false)` terminator, rather than
stored.

Because `w` is out of range for `Fin w`, the sentinel `(w, false)` can never
collide with a genuine entry `(pos.val, dir)`; that is what makes the encoding
readable back.

**Used in.** The inverse direction is `parseAux w hw_pos`
(`parseAux_triplesToAux`: `parseAux w hw_pos (triplesToAux w ts) = ts` for
`0 < w`). Together with `triplesToAux_append` (it is a monoid homomorphism on
lists) and `triplesToAux_markLast`, it supplies the injection used by
`exists_aux_injection`, the counting step of the switching-lemma encoding
argument. `triplesToAux` is `private` to `TCSlib/BooleanAnalysis/Switching.lean`.

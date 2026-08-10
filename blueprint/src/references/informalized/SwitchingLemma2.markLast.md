<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: markLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Tagging the last entry of a block

**Definition.** `markLast : List (Fin w × Bool) → List (Fin w × Bool × Bool)`
(`private`) copies a block of `(position, direction)` pairs into triples
`(position, direction, flag)`, setting `flag = true` on the final entry only:

- `[] ↦ []`;
- `[hd] ↦ [(hd.1, hd.2, true)]`;
- `hd :: hd2 :: rest ↦ (hd.1, hd.2, false) :: markLast (hd2 :: rest)`.

The `true` flag is what `triplesToAux` later renders as an explicit
`(w, false)` termination marker, so `markLast` is the bookkeeping device that makes
clause boundaries recoverable from a flat encoding.

Its three companion lemmas: `markLast_ne_nil` (nonempty in, nonempty out),
`markLast_length` (length preserved, by structural recursion), and
`markLast_getLast_true` (`((markLast block).getLast _).2.2 = true`, via
`List.getLast_cons`). `triplesToAux_markLast` states the round-trip form
`triplesToAux w (markLast block) = block.map (fun p => (p.1.val, p.2)) ++ [(w, false)]`
for nonempty `block`.

**Used in.** `exists_aux_injection` and the counting chain leading to
`bad_count_bound` / `switching_lemma`, where blocks of decision-path entries are
serialized into a single aux list that must be uniquely parseable (`parseAux`).

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: parseAux_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# parseAux on the empty aux list

**Claim.** For any width `w` with `0 < w`, `parseAux w hw_pos [] = []`.

**Proof.** Immediate from `rw [parseAux]` — this is the first defining equation of
`parseAux`, unfolded to close the goal by `rfl`.

**Used in.** A granular equational helper for `parseAux`, the parser that reads an
aux list `List (ℕ × Bool)` back into marked triples `List (Fin w × Bool × Bool)`.
Because `parseAux` is defined by well-founded recursion (`termination_by l =>
l.length`) with a nested `match` and a `dite`, its equation lemmas are not
generated in usable form, so each case is stated by hand; this one supplies the
`nil` base case of `parseAux_triplesToAux`.

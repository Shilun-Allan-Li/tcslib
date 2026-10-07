<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: parseAux_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Parsing a one-entry aux list

**Claim.** For `0 < w`, an index `idx` with `h : idx < w` and a direction `dir`,
`parseAux w hw_pos [(idx, dir)] = [(⟨idx, h⟩, dir, false)]`: a single in-range
entry parses to a single triple carrying no termination marker.

**Proof.** One of the four equational lemmas for `parseAux`, and immediate.

1. `rw [parseAux]` unfolds the definition at the `(idx, dir) :: rest` pattern
   with `rest = []`, exposing the guard `if h : idx < w`.
2. `simp only [h, ↓reduceDIte]` discharges that guard using `h`, leaving the
   `match rest with | [] => [(⟨idx, h⟩, dir, false)]` arm, which is the goal.

**Used in.** `parseAux_triplesToAux` — the `hasMarker = false`, empty-tail case,
where the round-trip has to reduce `parseAux` on a length-one aux list.
Companion lemmas `parseAux_nil`, `parseAux_cons_marker` and
`parseAux_cons_nonmarker` cover the other shapes.

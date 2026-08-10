<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: parseAux -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Parsing a flat aux list back into marked triples

**Definition.** `parseAux (w : ℕ) (hw_pos : 0 < w) : List (ℕ × Bool) → List (Fin w × Bool × Bool)`
(`private`) is the decoder for the Razborov-style encoding: it reads a flat list of
`(index, direction)` entries and returns triples `(pos, dir, hasMarker)`, where
`hasMarker = true` records that the entry was immediately followed by an
out-of-range termination marker. By recursion on the list, with
`termination_by l => l.length`:

- `[] ↦ []`;
- `(idx, dir) :: rest` with `idx < w`: if `rest = []` emit `(⟨idx, _⟩, dir, false)`;
  if `rest = (idx', dir') :: rest'` with `idx' ≥ w`, emit
  `(⟨idx, _⟩, dir, true)` and continue on `rest'` (the marker is consumed);
  otherwise emit `(⟨idx, _⟩, dir, false)` and continue on `rest`;
- `(idx, dir) :: rest` with `idx ≥ w`: drop the entry and continue on `rest` — a
  marker not preceded by a real entry carries no information.

Since Lean's equation compiler does not unfold this definition well, four equational
lemmas are stated by hand — `parseAux_nil`, `parseAux_singleton`,
`parseAux_cons_marker`, `parseAux_cons_nonmarker` — each proved by `rw [parseAux]`
followed by `simp only` on the relevant decidable conditions.

The point of the definition is `parseAux_triplesToAux`: `parseAux w hw_pos` is a
left inverse of `triplesToAux w`, proved by induction on the triple list with a
two-level case split on the marker flags of the first two entries.

**Used in.** `exists_aux_injection`, where the round-trip
`triplesToAux ∘ parseAux = id` on well-formed aux lists is what makes the encoding
injective, hence in `aux_image_card_bound`, `bad_count_bound` and ultimately
`switching_lemma`.

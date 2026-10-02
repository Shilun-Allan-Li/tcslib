<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: parseAux_cons_marker -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# parseAux on an entry followed by a termination marker

**Claim.** Fix `w` with `0 < w`, an index `idx` with `h : idx < w`, a direction
`dir : Bool`, and a tail `rest : List (ℕ × Bool)`. Then
`parseAux w hw_pos ((idx, dir) :: (w, false) :: rest)` equals
`(⟨idx, h⟩, dir, true) :: parseAux w hw_pos rest`. That is, an in-range entry
immediately followed by the out-of-range marker `(w, false)` is parsed as a triple
whose flag is `true`, and both the entry and the marker are consumed.

**Proof.** A one-step unfolding.

1. `rw [parseAux]` exposes the body: a `dite` on `idx < w`, then a `match` on the
   tail, then an `if` on `idx' ≥ w` for the tail's head index `idx' = w`.
2. `simp only [h, ↓reduceDIte, ge_iff_le, le_refl, ↓reduceIte]` discharges both
   branches — `h` reduces the `dite` and `le_refl : w ≤ w` reduces the `if` into
   the marker branch.

**Used in.** Equation lemma for the `true`-flag case of `parseAux_triplesToAux`
(the round-trip `parseAux ∘ triplesToAux = id`), which underpins injectivity of
the Razborov aux encoding.

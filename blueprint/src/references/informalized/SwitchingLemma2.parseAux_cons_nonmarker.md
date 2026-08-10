<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: parseAux_cons_nonmarker -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# parseAux on an entry followed by a non-marker

**Claim.** Fix `w` with `0 < w`, indices `idx`, `idx'` with `h : idx < w` and
`h' : idx' < w`, directions `dir`, `dir'`, and a tail `rest`. Then
`parseAux w hw_pos ((idx, dir) :: (idx', dir') :: rest)` equals
`(⟨idx, h⟩, dir, false) :: parseAux w hw_pos ((idx', dir') :: rest)`. That is, an
in-range entry followed by another in-range entry yields flag `false`, and only the
first entry is consumed.

**Proof.** A one-step unfolding.

1. `rw [parseAux]` exposes the `dite` on `idx < w` and the inner `if idx' ≥ w`.
2. `have hnge : ¬ idx' ≥ w := not_le.mpr h'` records that the tail head is *not*
   a marker.
3. `simp only [h, ↓reduceDIte, ge_iff_le, hnge, ↓reduceIte]` selects the
   non-marker branch.

**Used in.** Equation lemma for the `false`-flag case of `parseAux_triplesToAux`;
it is applied twice there, once for each possible flag on the following entry.

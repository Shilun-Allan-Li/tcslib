<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Restriction.lean :: zipIdx_drop_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# An indexed entry sits at the head of the corresponding tail

**Claim.** For `t : List α`, `l : α` and `idx : ℕ`, if `(l, idx) ∈ t.zipIdx`
then `t.drop idx = l :: rest` for some `rest`. In words: if `zipIdx` reports `l`
at position `idx`, dropping `idx` entries leaves `l` in front.

**Proof.**

1. `obtain ⟨_, hidx, heq⟩ := List.mem_zipIdx h`, then `simp at hidx heq`, gives
   the index bound and `t[idx] = l`.
2. `hlt : idx < t.length` follows by `omega`.
3. `rw [heq]` and `exact ⟨List.drop (idx + 1) t, List.drop_eq_getElem_cons hlt⟩`:
   the witness tail is `t.drop (idx + 1)`, and `List.drop_eq_getElem_cons` is
   exactly the identity `t.drop idx = t[idx] :: t.drop (idx + 1)`.

**Remark.** A packaging lemma: it converts `zipIdx` membership, which is what the
encoding produces, into the `drop`-shaped form the decision-tree descent
consumes.

**Used in.** Heavily in `Switching/EncodingProperties.lean` (lines 334, 350,
435, 462, 485, 632) and in `Switching/RoundTrip.lean:87`, each time to expose the
literal at a recorded position as the head of the remaining term.

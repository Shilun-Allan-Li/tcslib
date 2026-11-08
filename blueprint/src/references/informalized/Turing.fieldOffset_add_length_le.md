<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.fieldOffset_add_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Field offset bound

**Claim.** For a finite list of fields and an index $j$ within the list, the offset of field $j$ plus that field's length is at most the length of the joined fields.

**Proof.** Since $j<|fs|$, the list of fields is nonempty. The total-offset identity (`Turing.length_joinFields_add_one`) says that the offset after all fields is the joined-list length plus one. The offsets are nondecreasing as the index increases: each successive offset adds a field length plus one, by the successive-offset formula (`Turing.fieldOffset_succ`), so the offset after field $j$ is at most the total offset. In particular, the offset before field $j$ plus its length plus one is at most the total offset. Substituting the total-offset identity and cancelling one from both sides gives the desired bound.

**Key facts.** `Turing.length_joinFields_add_one`, `Turing.fieldOffset_succ`.

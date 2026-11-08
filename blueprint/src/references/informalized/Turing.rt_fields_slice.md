<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_fields_slice -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Slice of a Joined Tape

**Claim.** For lists of fields `pre`, `gs`, and `post` with `gs` nonempty, the joined middle fields fit within the full joined list after the offset of the middle block, and their tape contents agree at every offset from $-1$ through their joined length.

**Proof.** Let the full list be the concatenation of `pre`, `gs`, and `post`. Each field of `gs` occurs in the full list at index `pre.length + j`. Splitting the sum that defines field offsets shows that the offset of this field in the full list is the offset of the middle block plus its offset within `gs`. The field-offset bound (`fieldOffset_add_length_le`), applied to the last middle field, together with the endpoint identities (`fieldOffset_succ` and `fieldOffset_length`), shows that the middle block's joined length fits within the full joined list after the block's starting offset. Now take any allowed position $p$. Coverage by a joined field (`rt_field_cover`) supplies a middle-field index $j$ for which $p$ lies between one position before that field and its endpoint. The field-content identity (`fieldsTape_field`) computes the full tape content at the shifted position from that field, and computes the middle tape content at $p$ from the same field. The offset decomposition makes these positions identical, so the two tape contents agree.

**Key facts.** `Turing.fieldOffset_add_length_le`, `Turing.fieldOffset_succ`, `Turing.fieldOffset_length`, `Turing.rt_field_cover`, `Turing.fieldsTape_field`.

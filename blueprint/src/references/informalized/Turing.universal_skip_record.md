<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalBlock.lean :: Turing.universal_skip_record -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact-Cost Skip of One Record

**Claim.** Skipping one serialized action record advances the table cursor by the record's length and reaches the continuation determined by whether the remaining-record count is zero, without changing the state tape or its cursor.

**Proof.** The record-shape identity expresses its bits as eight fixed fields followed by a unary next-state code and delimiter (`Turing.universal_record_shape`). Thus its length is eight plus one more than the number of unary ones. The fixed-field skipping result advances over the eight fields and enters unary skipping. Then the unary-skipping result consumes the unary portion and delimiter, advances the cursor by the remaining record length, and chooses the stated continuation according to whether the remaining-record count is zero (`Turing.universal_skip_fixed`, `Turing.universal_skip_unary`). The run-addition law composes these two phases (`Turing.MultiTapeTM.runFrom_add`).

**Key facts.** `Turing.universal_record_shape`, `Turing.universal_skip_fixed`, `Turing.universal_skip_unary`, `Turing.MultiTapeTM.runFrom_add`.

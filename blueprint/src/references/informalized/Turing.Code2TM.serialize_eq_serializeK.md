<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Codes2Tape.lean :: Turing.Code2TM.serialize_eq_serializeK -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of Machine Encodings

**Claim.** For every two-work-tape deterministic Turing machine $M$ with Boolean alphabet and a finite state set, its two-work-tape serialization equals its serialization using the general $k$-tape encoding with $k=2$.

**Proof.** Expand both serialization definitions. The general two-tape table serialization agrees with the specialized two-tape table serialization (`Turing.tableBitsK_two`), since both enumerate the same states and read-symbol combinations and encode the corresponding transition actions. The specialized action encoding also agrees with the general action encoding for two tapes (`Turing.actionBits₂_eq_actionBitsK`). Replacing these table and action encodings leaves the common outer pairing and initial-state encoding unchanged, yielding the claimed equality.

**Key facts.** `Turing.tableBitsK_two`, `Turing.actionBits₂_eq_actionBitsK`.

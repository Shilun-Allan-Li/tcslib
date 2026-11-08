<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.configurationCodec_eq_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Configuration Encoding

**Claim.** For two configurations on the same input satisfying the window condition, their configuration encodings are equal exactly when their states, input-head positions, work-tape contents, work-tape head positions, and output summaries are equal.

**Proof.** The coefficient bound gives enough code positions to represent every coordinate in the finite set of row bits (`codecBit_card_le`). Consequently, equality of the two padded code words is equivalent to equality of their bit functions (`codecWord_eq_iff`). The row-bit map is injective (`codecRowBits_injective`), so equality of these bit functions is equivalent to equality of the encoded rows. Finally, for configurations satisfying the window condition, equality of their rows is equivalent to equality of their core data and output summaries (`codecRowOf_eq_iff`). Combining these equivalences gives the claim.

**Key facts.** `Complexity.codecBit_card_le`, `Complexity.codecWord_eq_iff`, `Complexity.codecRowBits_injective`, `Complexity.codecRowOf_eq_iff`.

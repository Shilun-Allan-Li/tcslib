<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.CodeFormat.parseFull_serialize_pad -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parsing Padded Serializations

**Claim.** For every code $M$ and natural number $m$, parsing the serialization of $M$ followed by $m$ copies of $1$ succeeds and returns $M$ together with those remaining bits.

**Proof.** Write $M$ as an assembled code with state bound $n$, initial state $q$, and table $t$. Its serialization is the pair encoding of $n$'s binary representation and the unary encoding of $q$ followed by the table bits. Appending the padding can be absorbed into the second component of this pair encoding, so pair decoding recovers the binary representation and the suffix consisting of the unary code, table bits, and padding. Pair decoding and encoding are inverse in this direction (`pairDecode_pairEncode`), and the binary representation decodes back to $n$ (`codeBitsNat_bits`), so the binary consistency check passes. The table-length lower bound ensures that the guard check passes: the suffix contains the table bits, whose length is at least $F.\mathrm{guard}\,(n+1)$. The unary finite-state reader consumes the encoding of $q$ and leaves the table bits followed by the padding (`codeReadFin_append`). The table reader consumes exactly the table bits and leaves the padding, by its defining append property. Finally, every remaining bit is $1$, so the parser's last check succeeds and it returns the assembled code, namely $M$, with the padding as remainder.

**Key facts.** `Turing.pairDecode_pairEncode`, `Turing.codeBitsNat_bits`, `Turing.codeReadFin_append`.

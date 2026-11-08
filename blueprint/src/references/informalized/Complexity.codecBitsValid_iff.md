<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecBitsValid_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of Valid Codec Bits

**Claim.** A Boolean assignment satisfies the codec validity conditions exactly when it is the bit encoding of some row with the specified input, state, head positions, tape symbols, and output summary.

**Proof.** Suppose first that the assignment is valid. Its validity witnesses give an input-head position, a state (possibly absent), and one head position for each work tape. Build a row using those witnesses, taking each input bit directly from the assignment. At each work cell, record false if its false-symbol bit is true, otherwise record true if its true-symbol bit is true, and otherwise record no symbol. The validity condition forbidding both symbol bits from being true makes this choice reproduce both symbol bits; the head-position condition reproduces the third work bit. Likewise, choose the output summary to be accepting when the first summary bit is true, dead when the second is true, and empty when both are false. The validity condition on summary bits ensures these cases are consistent. The resulting row's encoding agrees with the assignment at every kind of bit position. Conversely, every row's encoding satisfies the validity conditions (`Complexity.codecRowBits_valid`): its head and state encodings select exactly one position, each work cell records at most one Boolean symbol, and its summary encoding never sets both bits. Hence the assignment is valid exactly when it is the encoding of a row.

**Key facts.** `Complexity.codecRowBits_valid`.

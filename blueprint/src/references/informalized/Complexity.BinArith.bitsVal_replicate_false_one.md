<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/PrimeFind.lean :: Complexity.BinArith.bitsVal_replicate_false_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of a Terminal One Bit

**Claim.** For every natural number $j$, the word of $j$ false bits followed by one true bit has value $2^j$.

**Proof.** Use the appended-bit identity (`bitsVal_append_singleton`) with the list of $j$ false bits and the final true bit. The value of the false-bit list is zero: by the zero-value criterion (`bitsVal_eq_zero_iff`), it suffices that this list contains no true bit, which it does. The appended-bit formula then leaves $0+1\cdot 2^j=2^j$.

**Key facts.** `Complexity.BinArith.bitsVal_append_singleton`, `Complexity.BinArith.bitsVal_eq_zero_iff`.

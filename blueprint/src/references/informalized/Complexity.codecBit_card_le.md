<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecBit_card_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Codec-Bit Count Bound

**Claim.** If $|Q|+6k+5\le C$, then the number of codec-bit positions is at most $C(s+n+1)$.

**Proof.** The exact count is $n+(n+2)+(|Q|+1)+3k(2s+1)+2$ (`Complexity.codecBit_card`). This is at most $(|Q|+6k+5)(s+n+1)$: expanding the work-tape term gives $6ks+3k$, and the remaining terms are bounded by the corresponding contributions from $n$, $s$, and the constant coefficient. The hypothesis $|Q|+6k+5\le C$, multiplied by the nonnegative quantity $s+n+1$, then gives the desired bound.

**Key facts.** `Complexity.codecBit_card`.

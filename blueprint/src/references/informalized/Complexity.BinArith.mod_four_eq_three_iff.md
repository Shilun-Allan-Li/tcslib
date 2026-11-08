<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Jacobi.lean :: Complexity.BinArith.mod_four_eq_three_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Value Modulo Four

**Claim.** If the binary value of $w$ is odd, then it is congruent to $3$ modulo $4$ exactly when the second bit of $w$, treating a missing bit as zero, is true.

**Proof.** The binary value modulo eight is determined by the first three bits (`Complexity.BinArith.bitsVal_mod_eight`), and its parity is determined by the first bit (`Complexity.BinArith.bitsVal_mod_two`). The assumed oddness therefore fixes the first bit to true. Split according to whether the second and third bits are true or false, including the default false values when either position is absent. In these cases the modulo-eight formula shows that the value is congruent to $3$ modulo $4$ precisely when the second bit is true; the third bit contributes a multiple of four and does not affect this condition.

**Key facts.** `Complexity.BinArith.bitsVal_mod_eight`, `Complexity.BinArith.bitsVal_mod_two`.

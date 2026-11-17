<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Div.lean :: Complexity.BinArith.polyTimeComputable_mod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Remainder

**Claim.** The function returning the binary expansion of the first decoded value modulo the second decoded value is polynomial-time computable, with the stated behavior when the divisor is zero.

**Proof.** First project the appropriate component from the state produced by the polynomial-time division loop, and normalize its binary representation using the polynomial-time normalization of bits. Both operations preserve polynomial-time computability under composition. The divisor-zero test is also polynomial-time computable, so a polynomial-time conditional selects the output.

When the decoded divisor is zero, the function `mod` returns the binary expansion of zero remainder, and the conditional branch supplies the normalized binary representation of zero. When the divisor is nonzero, it is positive; the division-loop specification states that the designated decoded component of the loop’s final state has value equal to the first decoded value modulo the divisor. Normalizing that component therefore gives exactly the binary expansion required by `mod`. Thus the conditional construction computes the desired function in polynomial time.

**Key facts.** `Complexity.BinArith.polyTimeComputable_slot3`, `Complexity.BinArith.polyTimeComputable_divLoop`, `Complexity.BinArith.polyTimeComputable_pairFstD`, `Complexity.BinArith.polyTimeComputable_pairSndD`, `Complexity.BinArith.polyTimeComputable_normBits`, `Complexity.BinArith.polyTimeComputable_isZero`, `Complexity.polyTimeComputable_ite`, `Complexity.PolyTimeComputable.comp`, `Complexity.BinArith.divLoop_spec`.

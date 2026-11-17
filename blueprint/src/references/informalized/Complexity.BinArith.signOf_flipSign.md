<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Jacobi.lean :: Complexity.BinArith.signOf_flipSign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Reversal by Bit Flip

**Claim.** Replacing the first bit of a string by its complement, and discarding its remaining bits, reverses its assigned sign.

**Proof.** The flipped string is the singleton containing the complement of the original first bit (with an empty string treated as having first bit $0$). If that bit was $0$, the original sign is $+1$ and the flipped sign is $-1$; if it was $1$, the signs are reversed. In either case the new sign is the negative of the original.

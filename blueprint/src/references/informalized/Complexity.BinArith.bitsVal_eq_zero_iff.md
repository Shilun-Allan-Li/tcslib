<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.bitsVal_eq_zero_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Binary Value Criterion

**Claim.** A finite Boolean word has binary value zero exactly when it contains no true bit.

**Proof.** Induct on the word. The empty word has value zero and contains no true bit. For a word with first bit $b$ and tail $w$, its value is $b$'s value plus twice the value of $w$. If $b$ is true, this sum is positive, and the word contains a true bit. If $b$ is false, its contribution is zero, so the sum vanishes exactly when the tail's value vanishes; by induction, that is exactly when the tail contains no true bit. Since the first bit is false in this case, this is equivalent to the whole word containing no true bit.

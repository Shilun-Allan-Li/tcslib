<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Jacobi.lean :: Complexity.BinArith.bitsVal_mod_eight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Value Modulo Eight

**Claim.** For every finite Boolean word, the remainder of its value upon division by $8$ is the weighted sum of its first three bits, with weights $1$, $2$, and $4$ and missing bits treated as false.

**Proof.** Apply the value-from-the-first-bit identity (`bitsVal_eq_headD`) to the word and to the word after dropping one bit, and then to the word after dropping two bits. Together these express the value as the first bit's value, plus twice the second bit's value, plus four times the value after dropping three bits. The first three bit values are each zero or one, so their weighted sum is between zero and seven. The remaining contribution is divisible by eight. Thus the remainder modulo eight is exactly that weighted sum; the head-with-default notation supplies zero for any missing bit.

**Key facts.** `Complexity.BinArith.bitsVal_eq_headD`.

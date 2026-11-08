<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean :: Complexity.BinArith.sub_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subtraction on Encoded Binary Inputs

**Claim.** For any natural numbers $a$ and $b$, applying the decoded subtraction operation to the pair encoding of their binary expansions yields the binary expansion of the truncated difference $a-b$.

**Proof.** The pair encoding doubles each bit in the first binary expansion, then places the separator $01$ before the second expansion. Decoding this format recovers the two original expansions, so the subtraction operation computes the binary expansion of the difference of their decoded values. Each expansion decodes to its original natural number by the identity that evaluating the binary expansion recovers the number (`Complexity.LogProg.bitsVal_bits`). Thus the computed value is $a-b$, and its binary expansion is the claimed result.

**Key facts.** `Complexity.LogProg.bitsVal_bits`.

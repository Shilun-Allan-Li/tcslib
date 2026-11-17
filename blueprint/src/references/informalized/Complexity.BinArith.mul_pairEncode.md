<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Mul.lean :: Complexity.BinArith.mul_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplication of encoded binary expansions

**Claim.** Applying the multiplication operation to the encoding of the binary expansions of $a$ and $b$ returns the binary expansion of $ab$.

**Proof.** The pair encoding decodes back to its two components, so the multiplication operation takes the values of $\operatorname{bits}(a)$ and $\operatorname{bits}(b)$ and returns the bit string for their product. Each encoded bit string has value equal to the number it represents (`bitsVal_bits`). Therefore the computed product is $ab$, and the result is $\operatorname{bits}(ab)$.

**Key facts.** `Complexity.LogProg.bitsVal_bits`.

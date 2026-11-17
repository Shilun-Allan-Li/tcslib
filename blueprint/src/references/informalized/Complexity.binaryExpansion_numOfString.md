<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHaltMachine.lean :: Complexity.binaryExpansion_numOfString -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Encoding of Bit Strings

**Claim.** For every finite bit string $s$, folding its bits from right to left using $b,n\mapsto 2n+b$, starting from $1$, produces a natural number whose most-significant-bit-first binary expansion is $1$ followed by $s$.

**Proof.** By the fold-to-bits identity (`bits_foldr_bit_one`), the number obtained by folding the reversed string has least-significant-bit-first expansion equal to the reversed string followed by the terminal true bit. Reversing this expansion, as required by `binaryExpansion`, gives the true bit followed by the original string.

**Key facts.** `Complexity.bits_foldr_bit_one`.

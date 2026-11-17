<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3c_bits_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of binary expansion

**Claim.** The map sending a natural number to its little-endian binary expansion is injective.

**Proof.** Decode a binary expansion by folding the operation that appends a binary digit, starting from zero. Induction using the binary-recursion decomposition of a natural number shows that decoding its expansion recovers that number: the zero case is immediate, and in the digit case the expansion is obtained by appending that digit, so the induction hypothesis gives the result. If two natural numbers have the same expansion, applying this decoding fold to both sides gives the same number on each side. Hence the numbers are equal.

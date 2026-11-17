<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_product_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary length of a product

**Claim.** For natural numbers $a$ and $b$, the binary word representing $ab$ has length at most the sum of the lengths of the binary words representing $a$ and $b$.

**Proof.** The proof uses the fact that if a natural number $n$ is less than $2^m$, then the length of its binary word is at most $m$ (`length_bits_le`). The binary representation bounds give $a<2^{|\mathrm{bits}(a)|}$ and $b<2^{|\mathrm{bits}(b)|}$. Multiplying these inequalities yields $ab<2^{|\mathrm{bits}(a)|+|\mathrm{bits}(b)|}$, using positivity of the second power factor. Applying the length bound to this strict inequality gives the desired estimate.

**Key facts.** `Complexity.LogProg.length_bits_le`.

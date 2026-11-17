<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHaltMachine.lean :: Complexity.bits_foldr_bit_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bits of a Folded Binary Word

**Claim.** For every finite bit string $xs$, folding its bits from right to left by $b,n\mapsto 2n+b$, starting from $1$, gives a number whose least-significant-first binary expansion is $xs$ followed by a final $1$.

**Proof.** Proceed by induction on $xs$. For the empty word, the fold is $1$, whose binary expansion is the one-bit word $[1]$. For a word $b::xs$, the fold is obtained by applying the binary-bit operation with leading bit $b$ to the fold of $xs$. The latter is positive, by the positivity of every such fold (\texttt{Complexity.foldr\_bit\_one\_pos}), so the binary-expansion rule for adjoining a bit applies. It prepends $b$ to the expansion of the tail fold; the induction hypothesis identifies that expansion as $xs$ followed by $1$.

**Key facts.** `Complexity.foldr_bit_one_pos`.

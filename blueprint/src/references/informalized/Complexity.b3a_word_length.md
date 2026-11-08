<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Constructible.lean :: Complexity.b3a_word_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the B3a Word

**Claim.** For every natural number $n$, the word formed by placing a true bit before the tail of the binary expansion of $n$ has length $\lfloor\log_2 n\rfloor+1$.

**Proof.** If $n=0$, its binary expansion is empty, so the constructed word is the one-bit word $[\mathrm{true}]$; its length is $1=\logSpace(0)$. If $n\ne0$, the binary expansion has length $\logSpace(n)$ by `b3a_bits_length`. Removing its first bit and prepending one true bit preserves that length, proving the claim.

**Key facts.** `Complexity.b3a_bits_length`.

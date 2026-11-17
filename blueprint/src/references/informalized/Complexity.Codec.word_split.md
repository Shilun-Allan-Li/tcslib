<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean :: Complexity.Codec.word_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Splitting at a final marked bit

**Claim.** If $|w|=a+b+1$ and the bit of $w$ at index $a+b$ is $1$, then $w$ is its first $a$ bits followed by the next $b$ bits and the one-bit string $1$.

**Proof.** The suffix of $w$ beginning at position $a+b$ has length one, by the given length equation. It is therefore a singleton, say $[c]$. Its first optional entry is the bit of $w$ at position $a+b$, so the marked-bit hypothesis forces $c=1$. Thus the suffix is $[1]$. Splitting the list first after $a+b$ entries and then splitting the initial segment after $a$ entries expresses $w$ as $w.take\ a ++ (w.drop\ a).take\ b ++ [1]$, as claimed.

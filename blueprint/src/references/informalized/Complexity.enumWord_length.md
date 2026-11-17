<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumWord_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed-Width Word Length

**Claim.** For all natural numbers $w$ and $i$, the width-$w$ little-endian binary word of $i$ has length exactly $w$.

**Proof.** Induct on the width $w$, allowing $i$ to be arbitrary. At width zero the word is empty, so its length is zero. At width $w+1$, the definition puts one bit in front of the width-$w$ word of the quotient. Its length is therefore one plus the length of that smaller word, which by induction is $w$; hence the length is $w+1$.

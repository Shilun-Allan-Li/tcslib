<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5ReadInput_get -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering an Assigned Input Bit

**Claim.** For $j<m$, the bit at position $j$ in the word formed from the first $m$ assigned bits is $a(j)$.

**Proof.** The word is formed by listing the values $a(i)$ for indices $i$ in the finite interval from $0$ to $m-1$. At an index $j<m$, list lookup therefore returns $a(j)$; the default value is irrelevant because the index is in range.

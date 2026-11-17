<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clPair_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending to a paired word

**Claim.** For Boolean words $a,b,c$, appending $c$ to the encoding of $(a,b)$ gives the encoding of $(a,b c)$: $\langle a,b\rangle c=\langle a,b c\rangle$.

**Proof.** By definition, the pair encoding consists of the doubled-bit encoding of $a$, followed by the fixed separator, followed by $b$. Appending $c$ therefore leaves the first two parts unchanged and changes the final part from $b$ to $b c$. Associativity of list concatenation gives exactly the encoding of $(a,b c)$.

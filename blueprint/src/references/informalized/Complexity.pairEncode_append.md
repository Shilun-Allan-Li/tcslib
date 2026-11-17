<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.pairEncode_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending to a Pair Encoding

**Claim.** Appending $c$ to the pair encoding of $a$ and $b$ gives the pair encoding of $a$ and $bc$.

**Proof.** By definition, the pair encoding consists of the doubled string $a$, followed by the separator $01$, followed by $b$. Appending $c$ therefore gives the doubled $a$ and separator followed by $bc$, which is exactly the pair encoding of $a$ and $bc$. Associativity of concatenation justifies regrouping the lists.

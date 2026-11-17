<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_pair_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair encoding of concatenated words

**Claim.** Encoding the pair whose first component is $a++b$ and second component is $u$ gives the doubled bits of $a$ followed by the encoding of $(b,u)$.

**Proof.** The encoding first duplicates every bit of its first component, then appends the fixed separator and the second component. Duplicating the bits of $a++b$ yields the concatenation of the duplicated bits of $a$ with those of $b$. Associativity of concatenation then groups the latter part together with the separator and $u$, which is precisely the encoding of $(b,u)$.

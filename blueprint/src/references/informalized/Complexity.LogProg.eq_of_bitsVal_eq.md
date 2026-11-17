<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean :: Complexity.LogProg.eq_of_bitsVal_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of Binary Words

**Claim.** Two finite Boolean words of equal length with the same binary value are equal.

**Proof.** Proceed by induction on the words, using their common length. If both are empty, they are equal. Otherwise write them as $x::a$ and $y::b$. Their values are $x+2\,\mathrm{bitsVal}(a)$ and $y+2\,\mathrm{bitsVal}(b)$. Reducing the equality modulo $2$ shows that $x$ and $y$ have the same parity; since each is a Boolean bit, this forces $x=y$. After removing the common head, equality of the original values gives $2\,\mathrm{bitsVal}(a)=2\,\mathrm{bitsVal}(b)$, hence the suffix values agree by cancellation. The suffixes also have equal length, so the induction hypothesis gives $a=b$, and therefore the original words are equal.

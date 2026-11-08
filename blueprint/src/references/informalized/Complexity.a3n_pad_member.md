<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_pad_member -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in the Padded Language

**Claim.** For every Boolean word $x$, its pair encoding with the prescribed all-ones padding belongs to the padded language of $L$ if and only if $x$ belongs to $L$.

**Proof.** By definition, membership of this encoded word means that it equals the pair encoding of some word $y$ together with the all-ones padding prescribed for $y$, where $y\in L$. Injectivity of pair encoding (`Turing.pairEncode_injective`) forces the first components to agree, so $x=y$ and therefore $x\in L$. Conversely, if $x\in L$, choose $x$ itself as the witnessing word in the definition of the padded language; the required equality of encodings is immediate.

**Key facts.** `Turing.pairEncode_injective`.

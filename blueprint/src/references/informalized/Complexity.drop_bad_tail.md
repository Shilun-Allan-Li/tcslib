<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.drop_bad_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection of a Noncanonical Tail

**Claim.** If $tail$ is not canonical, then the indicator of the transformed-input language is false on the encoding of $z$ and $tail$, for either mode.

**Proof.** Suppose the encoding of $z$ and $tail$ belonged to the language. Then it would also be an encoding of some string $w$ paired with the binary representation of a natural number $q$. Injectivity of pair encoding (Turing.pairEncode_injective) forces the two components to agree, in particular $tail=\mathrm{Nat.bits}(q)$. Every natural number's binary representation is canonical (Complexity.LogProg.canon_bits), contradicting the assumption that $tail$ is not canonical. Hence the encoded input is outside the language, so its indicator is false.

**Key facts.** `Turing.pairEncode_injective`, `Complexity.LogProg.canon_bits`.

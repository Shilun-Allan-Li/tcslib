<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean :: Complexity.LtM.orc_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership of Encoded Strings

**Claim.** For natural numbers $n$ and $v$, the oracle returns true on the pairing of the unary string of length $n$ with the bit string of $v$ exactly when $v=2n$.

**Proof.** The oracle is the Boolean indicator of the language consisting of encodings of a unary string of length $n'$ paired with the bit representation of $2n'$. Its value on the given input is therefore the decision of whether that input belongs to this language (`Complexity.LogProg.indicator_eq_decide`). Membership supplies some $n'$ for which the two encoded pairs are equal. Uniqueness of the unary length and payload in such an encoding (`Turing.pairEncode_replicate_inj`) gives $n'=n$ and $\mathrm{bits}(v)=\mathrm{bits}(2n)$. Injectivity of the bit representation (`Complexity.LogProg.bits_injective`) yields $v=2n$. Conversely, if $v=2n$, the given input itself is a language witness with index $n$, proving membership and hence that the oracle returns true.

**Key facts.** `Complexity.LogProg.indicator_eq_decide`, `Turing.pairEncode_replicate_inj`, `Complexity.LogProg.bits_injective`.

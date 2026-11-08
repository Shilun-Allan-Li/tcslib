<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean :: Complexity.mem_unaryIdx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in the Encoded Index Set

**Claim.** The string formed by pairing $n$ copies of $1$ with the binary bit string of $i$ belongs to the set of strings encoding a pair satisfying $p$ exactly when $p(n,i)$ holds.

**Proof.** If the string belongs to the set, it equals the encoding of some pair $(n',i')$ for which $p(n',i')$ holds. Injectivity of the pairing encoding on unary first components (`Turing.pairEncode_replicate_inj`) gives $n'=n$ and equality of the two binary strings. Injectivity of the map sending a natural number to its binary bit string (`Complexity.LogProg.bits_injective`) then gives $i'=i$. Thus $p(n,i)$ holds. Conversely, if $p(n,i)$ holds, the string itself witnesses membership, using the pair $(n,i)$.

**Key facts.** `Turing.pairEncode_replicate_inj`, `Complexity.LogProg.bits_injective`.

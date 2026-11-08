<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ZeroSpace.lean :: Turing.pairEncode_bits_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Pair Encoding on Binary Expansions

**Claim.** For all bit strings $x,y$ and natural numbers $i,j$, the encodings of $x$ paired with the binary expansion of $i$ and $y$ paired with the binary expansion of $j$ are equal if and only if $x=y$ and $i=j$.

**Proof.** If the two encodings are equal, injectivity of the pair encoding on pairs of bit strings gives equality of both components (`Turing.pairEncode_injective`). Equality of the first components says $x=y$; equality of the second says that the binary expansions of $i$ and $j$ agree, which implies $i=j$ because the map sending a natural number to its binary expansion is injective (`Complexity.LogProg.bits_injective`). Conversely, if $x=y$ and $i=j$, both component strings agree, so their pair encodings are equal by substitution.

**Key facts.** `Turing.pairEncode_injective`, `Complexity.LogProg.bits_injective`.

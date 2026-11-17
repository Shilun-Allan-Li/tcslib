<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.polyTimeComputable_pairSwap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Pair Swap

**Claim.** The map sending a bit string $z$ to the encoding of its total second projection followed by its total first projection is polynomial-time computable; either projection is the empty word when parsing fails.

**Proof.** Both total projections are polynomial-time computable: the first-projection theorem supplies this for the first component (`polyTimeComputable_pairFstD`), and the second-projection theorem supplies it for the second (`polyTimeComputable_pairSndD`). The closure theorem for pairing says that polynomial-time computable component functions can be combined by the pairing encoding (`PolyTimeComputable.pairEncode`). Applying it with the second projection as the first encoded component and the first projection as the second encoded component gives the stated swap.

**Key facts.** `Complexity.polyTimeComputable_pairSndD`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.pairEncode`.

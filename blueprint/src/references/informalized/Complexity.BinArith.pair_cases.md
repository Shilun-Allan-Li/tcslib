<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.pair_cases -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair-Decoding Alternatives

**Claim.** For every bit string $z$, either both total projections of $z$ are empty, or $z$ is the pair encoding of its total first and second projections.

**Proof.** Split according to whether decoding $z$ succeeds. If it fails, each total projection defaults to the empty list, giving the first alternative. If decoding succeeds with components $a$ and $b$, the decoding reconstruction property says that $z$ is the pair encoding of $a$ and $b$ (the fact that decoding returns those components is `Turing.eq_pairEncode_of_pairDecode`). The total projections are exactly $a$ and $b$, so the second alternative follows.

**Key facts.** `Turing.eq_pairEncode_of_pairDecode`.

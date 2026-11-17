<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.length_pair_components_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoded Pair Length Bound

**Claim.** For every bit string $y$, the total first and second projections of its decoding satisfy $2|\pi_1(y)|+|\pi_2(y)|\le |y|$, with both projections taken to be empty if decoding fails.

**Proof.** Split according to whether decoding succeeds. If it fails, both default projections are empty, so the left side is zero. If decoding succeeds with components $p$ and $u$, the decoding characterization says that $y$ is exactly the pair encoding of $p$ and $u$ (`eq_pairEncode_of_pairDecode`). The projections of that encoding recover $p$ and $u (`pairFstD_pairEncode`, `pairSndD_pairEncode`), while its length is $2|p|+2+|u|$ (`length_pairEncode`). Thus the desired bound follows, with the encoding's two delimiter bits providing the extra length.

**Key facts.** `Turing.eq_pairEncode_of_pairDecode`, `Turing.length_pairEncode`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.

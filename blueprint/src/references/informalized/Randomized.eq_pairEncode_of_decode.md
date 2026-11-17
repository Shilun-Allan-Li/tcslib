<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPPIT.lean :: Randomized.eq_pairEncode_of_decode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair decoding recovers the input encoding

**Claim.** If decoding the first total projection of a binary string yields a dimension together with an algebraic circuit, then the string is the self-delimiting encoding of its two total projections.

**Proof.** Split according to whether pair decoding of $x$ fails or returns a pair. If it fails, the first total projection is the empty string. The assumed successful circuit decoding of that projection is impossible, since the empty string has no circuit decoding. If pair decoding returns $(a,b)$, the pair-decoding reconstruction theorem gives $x=\operatorname{pairEncode}(a,b)$ (`eq_pairEncode_of_pairDecode`). In this case the total projections are exactly $a$ and $b$, so substituting them yields $x=\operatorname{pairEncode}(\operatorname{pairFstD}(x),\operatorname{pairSndD}(x))$, as required.

**Key facts.** `Turing.eq_pairEncode_of_pairDecode`.

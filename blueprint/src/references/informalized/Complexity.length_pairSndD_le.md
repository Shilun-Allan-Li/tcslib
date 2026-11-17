<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.length_pairSndD_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Projection Length Bound

**Claim.** For every finite bit string $z$, its total second projection has length at most $|z|$.

**Proof.** If decoding fails, the total second projection is empty, so the inequality holds. If decoding succeeds with components $a,b$, the decoded representation theorem identifies $z$ with the encoding of $(a,b)$ (`Turing.eq_pairEncode_of_pairDecode`), and the second projection of that encoding is $b$ (`Complexity.pairSndD_pairEncode`). The encoding length is $2|a|+2+|b|$ (`Turing.length_pairEncode`), which is at least $|b|$. Therefore the second projection has length at most $|z|$.

**Key facts.** `Turing.eq_pairEncode_of_pairDecode`, `Complexity.pairSndD_pairEncode`, `Turing.length_pairEncode`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.length_pairFstD_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Projection Length Bound

**Claim.** For every finite bit string $z$, its total first projection has length at most $|z|$.

**Proof.** If decoding $z$ fails, its total first projection is empty, so the bound is immediate. If decoding succeeds with components $a,b$, then $z$ is exactly their encoding (`Turing.eq_pairEncode_of_pairDecode`). The first projection of that encoding is $a$, and the encoding has length $2|a|+2+|b|$ (`Turing.length_pairEncode`). In particular, $|a|\le |z|$, which proves the claim.

**Key facts.** `Turing.eq_pairEncode_of_pairDecode`, `Turing.length_pairEncode`.

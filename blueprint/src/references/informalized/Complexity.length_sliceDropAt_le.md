<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.length_sliceDropAt_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dropped Slice Length Bound

**Claim.** For natural numbers $a$ and $k$ and any bit string $z$, encoding the first component of its total pair decoding with the specified dropped suffix of the second component produces a string of length at most $\max(|z|,2)$.

**Proof.** Split according to whether decoding $z$ succeeds. If it fails, both default components are empty. The resulting encoding has length two, so it is at most $\max(|z|,2)$. If decoding succeeds with components $p$ and $u$, then $z$ is the pair encoding of $p$ and $u$ (`eq_pairEncode_of_pairDecode`), and its projections recover those components (`pairFstD_pairEncode`, `pairSndD_pairEncode`). The resulting string encodes $p$ together with a suffix of $u$ after dropping the prescribed number of bits. Dropping bits cannot increase a list's length, so the encoded result has length at most $2|p|+2+|u|$, the length of the encoding of $(p,u)$ (`length_pairEncode`). This is $|z|$, hence the bound by the maximum also holds.

**Key facts.** `Turing.eq_pairEncode_of_pairDecode`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Turing.length_pairEncode`.

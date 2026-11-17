<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.length_pairEncode_drop_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for Encoded Dropped Projections

**Claim.** For any bit string $s$ and natural numbers $i,j$, encoding the first and second total projections after dropping $i$ and $j$ bits has length at most $\max(|s|,2)$.

**Proof.** Split according to whether decoding $s$ fails or succeeds. If it fails, both total projections are empty. Dropping bits leaves them empty, and encoding the empty pair has length $2$, which is at most $\max(|s|,2)$. If decoding succeeds with components $a,b$, the decoded representation theorem says that $s$ is exactly the encoding of $(a,b)$ (`Turing.eq_pairEncode_of_pairDecode`). The total projections of an encoded pair recover its two components (`Complexity.pairFstD_pairEncode` and `Complexity.pairSndD_pairEncode`). Thus the strings being encoded after dropping are $a$ with $i$ bits removed and $b$ with $j$ bits removed. Dropping cannot increase either length, so the encoding length, $2|a\mathbin{\mathrm{drop}}i|+2+|b\mathbin{\mathrm{drop}}j|$, is at most $2|a|+2+|b|=|s|$, by the encoding length formula (`Turing.length_pairEncode`). Hence it is at most the stated maximum.

**Key facts.** `Turing.eq_pairEncode_of_pairDecode`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Turing.length_pairEncode`.

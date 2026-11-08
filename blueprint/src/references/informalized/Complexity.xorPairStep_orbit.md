<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.xorPairStep_orbit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orbit of the Pair Step

**Claim.** After $i$ applications of the pair-step map to the encoding of $(p,u)$, the result is the encoding of the pair formed by deleting the first $i$ bits of each string.

**Proof.** Induct on $i$. At zero applications the statement holds because deleting zero bits leaves both strings unchanged. For the successor step, first apply the induction hypothesis: the current encoding is that of $(p.drop\ i,u.drop\ i)$. The pair-step map decodes this encoding to those two suffixes, deletes the first bit of each, and re-encodes them. Deleting one bit from each suffix after dropping $i$ bits is the same as dropping $i+1$ bits from the original strings, giving the result.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.

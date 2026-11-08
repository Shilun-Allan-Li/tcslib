<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonPrefix.lean :: Complexity.KarpLipton.mem_prefixLangOf_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Membership After a Marker Run

**Claim.** The encoding of $y$ paired with $k$ ones followed by $0p$ belongs to the prefix language exactly when some suffix $s$ makes $ps$ have length $\ell(y)$ and makes the encoding of $y$ paired with $ps$ belong to $V$.

**Proof.** Apply the membership characterization for the prefix language (`mem_prefixLangOf`). The total projections of an encoded pair recover its two components (`pairFstD_pairEncode` and `pairSndD_pairEncode`), so the projections here are $y$ and the string consisting of $k$ ones followed by $0p$. Dropping that marker run leaves exactly $p` (`dropMarker_marker`). Substitution gives the asserted existential condition.

**Key facts.** `Complexity.KarpLipton.mem_prefixLangOf`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.KarpLipton.dropMarker_marker`.

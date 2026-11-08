<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean :: Complexity.eq_pathRaw_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of the Raw Path Encoding

**Claim.** The raw path encoding equals $x$ exactly when the three doubled segments and final plain segment occur at the stated positions, with the stated false padding convention and exact final length.

**Proof.** First suppose $x$ is the raw path encoding. Dropping the initial encoded segment of $n$ true bits leaves the encoding of $M$ paired with the two encoded binary expansions. Dropping the next encoded segment leaves the nested encoding of the expansions of $s$ and $t$, and dropping the encoded $s$ segment leaves precisely the bits of $t$. These successive tail identities follow from the fact that dropping a paired encoding past its doubled data and separator recovers its second component (`Complexity.drop_pairEncode`). The characterization of a doubled segment by its tail (`Complexity.dblAt_iff`) now gives each of the three doubled-segment conditions. The characterization of a plain segment by its tail and endpoint (`Complexity.plainAt_iff`) gives the final bit condition and exact length; the length formula for a paired encoding (`Turing.length_pairEncode`) supplies that endpoint.

Conversely, suppose all four segment conditions hold. By `Complexity.dblAt_iff`, each doubled-segment condition identifies the corresponding tail as the pairing of that segment's word with the tail after its separator. By `Complexity.plainAt_iff`, the last condition identifies the final tail with the bits of $t$ and fixes the end of $x$. Substituting these tail descriptions in order reconstructs the nested paired encoding, so $x$ is exactly the raw path encoding.

**Key facts.** `Complexity.drop_pairEncode`, `Complexity.dblAt_iff`, `Complexity.plainAt_iff`, `Turing.length_pairEncode`.

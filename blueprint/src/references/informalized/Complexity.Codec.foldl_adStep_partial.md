<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Scan.lean :: Complexity.Codec.foldl_adStep_partial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Processing a partial buffer segment

**Claim.** If $j+|l|\le w$, processing $l$ from position $j$ leaves the state unchanged, advances the position to $j+|l|$, and writes each entry of $l$ into its corresponding buffer position.

**Proof.** Induct on $l$, allowing the starting position and buffer to vary. For the empty list, no update occurs; the position remains $j$, and there are no entries whose buffer contents need to be checked. For $a::l$, the bound $j+|a::l|\le w$ implies $j<w$, so the first update does not complete a full block. It leaves the state unchanged, advances the position to $j+1$, and writes $a$ at position $j$. Apply the induction hypothesis to $l$ starting at $j+1$ with this updated buffer. It gives the claimed final position and entries for all positions written by the tail. At position $j$, the first entry $a$ remains in the buffer: every later update writes at a position strictly greater than $j$, so it cannot overwrite that entry. At any position in the segment strictly after $j$, the induction hypothesis identifies the buffer entry with the corresponding entry of $l$; shifting its index by one identifies it with the corresponding entry of $a::l$. Thus every position in the whole segment contains the required list entry.

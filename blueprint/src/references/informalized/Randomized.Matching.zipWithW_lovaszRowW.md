<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Matching.lean :: Randomized.Matching.zipWithW_lovaszRowW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoded Lovász Sample Matrix

**Claim.** Under the stated length conditions, the encoded row procedure yields the encoding of the matrix whose entries are the specified binary block values when the corresponding adjacency bit is true, and zero otherwise.

**Proof.** Write $n=|u|$ and $k=|K|$. The chunking identity says that a pair encoding a word of length $N|c|$ splits into the encoding of its $N$ consecutive blocks of length $|c|$ ( `chunkW_pairEncode`). Applying it to $(u,w)$ and $(NK,r)$ gives the row-wise adjacency and sample blocks. The hypotheses ensure the required block lengths; if $K$ is empty, the alternative hypothesis forces $u$ to be empty, which is the degenerate case covered by the chunking identity.

The encoded zip-with identity then says that the outer procedure applies $lovaszRowW$ to corresponding decoded blocks and re-encodes the results ( `zipWithW_pairEncode`). Decoding words after encoding recovers the original list ( `decWords_encWords`), and the pair projections recover the components of each pair encoding ( `pairFstD_pairEncode`, `pairSndD_pairEncode`). Thus it remains to identify the entry at row $i$, column $j$.

The length hypotheses ensure that the row's adjacency block has a bit at position $j$, equal to $w_{ni+j}$, and that the row's sample block contains the length-$k$ segment of $r$ starting at $(ni+j)k$. The entry procedure returns the binary value of that segment when the adjacency bit is true, and zero when it is false. This is precisely the stated definition of the matrix entries. Therefore every row agrees, and their encodings agree as well.

**Key facts.** `Complexity.BinArith.chunkW_pairEncode`, `Complexity.BinArith.zipWithW_pairEncode`, `Complexity.BinArith.decWords_encWords`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.

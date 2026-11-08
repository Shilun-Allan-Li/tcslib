<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Matching.lean :: Randomized.Matching.encodeBPM_mem_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding membership and perfect matchings

**Claim.** The encoding of a word of $n$ ones together with the row-by-row adjacency word of $A$ belongs to the language of encoded bipartite graphs with perfect matchings exactly when the graph associated with $A$ has a perfect matching.

**Proof.** If the encoding belongs to the language, it equals some encoding formed from a word of $m$ ones and a matrix $B$ with a perfect matching. Apply the first-component parser and take lengths. The parser recovers the original first component (pairFstD_pairEncode), so this equality gives $n=m$. Next apply the second-component parser and decode its adjacency word as an $n\times n$ matrix. The parser recovers that second component (pairSndD_pairEncode), and decoding the row-by-row adjacency word recovers its matrix (adjOfWord_adjWord); hence $B=A$. The perfect matching of $B$ therefore gives one for $A$. Conversely, a perfect matching for $A$ witnesses language membership directly, using the same $n$, the same matrix $A$, and its defining encoding.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Randomized.Matching.adjOfWord_adjWord`.

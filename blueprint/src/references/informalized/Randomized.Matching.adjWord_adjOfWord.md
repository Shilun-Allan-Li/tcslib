<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Matching.lean :: Randomized.Matching.adjWord_adjOfWord -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering a Word from Its Matrix

**Claim.** If a bit string has length $n^2$, then taking the adjacency word of the matrix decoded from it recovers the original string.

**Proof.** The proof establishes equality of the two lists by comparing entries at each position $m$. The adjacency word has length $n^2$ (Randomized.Matching.length_adjWord), so the given length hypothesis makes the entry comparison valid for every position of the original word. Since the word has length $n^2$, we have $n>0$; write $m=(m/n)n+(m\bmod n)$. The quotient is less than $n$, and the remainder is less than $n$. The indexing lemma for adjacency words (Randomized.Matching.getD_adjWord), applied to the decoded matrix at these two indices, identifies the corresponding adjacency-word entry with the original word at position $m$. Thus every entry agrees, and the lists are equal.

**Key facts.** `Randomized.Matching.length_adjWord`, `Randomized.Matching.getD_adjWord`.

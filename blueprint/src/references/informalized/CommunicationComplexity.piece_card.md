<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Hamming.lean :: CommunicationComplexity.piece_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equal sizes of support-fiber slices

**Claim.** For each symbol $a\ne u_i$, the words in the support fiber over $\{i\}\cup S$ whose entry at $i$ is $a$ have the same cardinality as the support fiber over $S$, provided $i\notin S$.

**Proof.** Fix such a symbol $a$. Map each word $v$ in the indicated slice to the word obtained by resetting its entry at $i$ to $u_i$. Since $v_i=a\ne u_i$, the support of this reset word is precisely the support of $v$ with $i$ removed, namely $S$. Thus the map lands in the fiber over $S$. It is injective on the slice: away from $i$ it leaves every entry unchanged, and at $i$ all words in the slice have the same entry $a$. For surjectivity, take any word $b$ in the fiber over $S$ and change its entry at $i$ to $a$. Because $i\notin S$ and $a\ne u_i$, the resulting word has support exactly $\{i\}\cup S$; resetting its entry at $i$ recovers $b$. Hence the reset map is a bijection between the slice and the fiber over $S$, so their cardinalities agree.

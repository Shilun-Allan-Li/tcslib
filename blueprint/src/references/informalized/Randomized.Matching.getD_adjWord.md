<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Matching.lean :: Randomized.Matching.getD_adjWord -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adjacency Word Entries

**Claim.** For indices $i,j<n$, the entry at position $in+j$ of the row-by-row list of entries of $A$ is $A_{ij}$.

**Proof.** First prove the assertion with the outer row list replaced by any list $L$ of row indices: at position $in+j$, the flattened list contains the entry of row $L[i]$ in column $j$. Induct on $L$. The empty list has no valid row index. For a nonempty list, if $i=0$, the requested position lies in the first mapped row; since $j<n$, the list lookup selects its $j$th entry, namely $A_{L[0],j}$. If $i=i'+1$, the position is $n+(i'n+j)$. The first mapped row has length $n$, so this position lies in the remaining flattened rows, with offset $i'n+j$ there. The induction hypothesis gives $A_{L[i'],j}$ in the tail, which is exactly the entry indexed by $i$ in $L$. Finally take $L$ to be the list of all indices from $0$ to $n-1$; its $i$th entry is $i$, yielding the claim.

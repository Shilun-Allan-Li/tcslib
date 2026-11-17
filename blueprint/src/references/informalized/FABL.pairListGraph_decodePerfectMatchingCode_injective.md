<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.pairListGraph_decodePerfectMatchingCode_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of matching-code decoding

**Claim.** For a repetition-free vertex list of length $2m$, the graph obtained by decoding a perfect-matching code determines the code uniquely.

**Proof.** Proceed by induction on $m$, allowing the vertex list to vary while keeping its required length and absence of repetitions. When $m=0$, the code type has only one element, so injectivity is immediate.

For the induction step, write the list as $x::xs$. Each code begins with an index into $xs$, followed by a smaller code. Decoding produces the first pair $(x,y)$, where $y$ is the indexed element, followed by the decoded pairs on the list obtained by deleting that indexed element. The index is in range because $xs$ has length $2m+1$. The decoded pairs use every element of their input list exactly once: this is the permutation fact for flattening a decoded code (`flattenPairList_decodePerfectMatchingCode_perm`). In particular, the endpoints in the smaller decoding cannot include $x$.

Suppose two codes give the same graph. The first decoded edge from the first code is an adjacency from $x$ to its chosen endpoint $y$. The adjacency characterization for a pair-list graph (`pairListGraph_adj_iff`) says that this edge must occur in the second decoded list, in one orientation. It cannot come from the second code's smaller list, since that list's endpoints exclude $x$; nor can the reversed first edge be the match, since the first edge has distinct endpoints. Thus the two first endpoints agree. Since $xs$ has no repetitions, equal selected elements have equal indices, so the initial indices agree.

Now the two codes delete the same entry from $xs$, giving the same remaining list. Their smaller decoded graphs also agree: any adjacency in either smaller graph is an adjacency in the full graph, and the only extra edge in that full graph is the common first pair. That pair cannot occur among the smaller edges, because their endpoints exclude $x$. Applying the adjacency characterization in both directions therefore gives equality of the smaller graphs. The remaining list still has length $2m$ and no repetitions, so the induction hypothesis makes the remaining codes equal. Together with equality of the initial indices, the original codes are equal.

**Key facts.** `FABL.flattenPairList_decodePerfectMatchingCode_perm`, `FABL.pairListGraph_adj_iff`.

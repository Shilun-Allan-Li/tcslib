<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.flattenPairList_decodePerfectMatchingCode_perm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoded endpoints form a permutation

**Claim.** For a perfect-matching code of size $m$ and a list of length $2m$, flattening the decoded pairs gives a permutation of the original list.

**Proof.** Proceed by induction on $m$, allowing the vertex list to vary. When $m=0$, the length condition forces the list to be empty, and decoding and flattening both yield the empty list. For the inductive step, write the code as a first choice $j$ and a remaining code, and write the vertex list as $x::xs$. Its length condition gives $|xs|=2m+1$. Since $j$ is an index among the $2m+1$ positions of $xs$, the selected element $xs[j]$ exists. Removing that position leaves a list of length $2m$, so the induction hypothesis says that decoding the remaining code from this shortened list and flattening its pairs gives a permutation of the shortened list. The full flattened output begins with $x,xs[j]$, followed by that inductive output. Reinsert $xs[j]$ into the shortened list using the fact that an element at a valid index, followed by the list with that index erased, is a permutation of the original list (`List.getElem_cons_eraseIdx_perm`). Prepending $x$ to both sides of the resulting permutation proves the claim.

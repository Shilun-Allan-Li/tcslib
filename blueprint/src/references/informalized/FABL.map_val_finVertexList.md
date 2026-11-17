<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.map_val_finVertexList -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values of the Finite Vertex List

**Claim.** Mapping the values of the entries in the list of all elements of $\{0,\ldots,N-1\}$ gives the list $0,1,\ldots,N-1$.

**Proof.** Compare the two lists by their lengths and entries at each valid position. The list of finite vertices is defined by enumerating the identity function on $\mathrm{Fin}(N)$, so its $i$th entry is the vertex with value $i$. Applying the value map therefore yields $i$, which is also the $i$th entry of the range list. The lengths agree as well, so the lists are equal.

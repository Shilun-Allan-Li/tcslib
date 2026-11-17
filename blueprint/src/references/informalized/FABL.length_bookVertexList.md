<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.length_bookVertexList -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the book vertex list

**Claim.** For all natural numbers $q$ and $k$, the book vertex list has length $qk$.

**Proof.** The list begins with the list of all elements of the finite set of size $qk$, whose length is $qk$. Each element is then mapped through the inverse of the vertex equivalence; mapping does not change list length. Therefore the book vertex list has length $qk$.

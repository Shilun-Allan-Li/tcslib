<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.LevelKParityTuple.assignedVertexLabel_injective_on_part -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity within a part

**Claim.** For each fixed part, the vertex label is injective as a function of the position.

**Proof.** Take positions $a,b$ whose labels agree. By the definition of the assigned label, these are the underlying elements of the enumerated points corresponding to the permuted positions. Equality of the underlying elements gives equality of the two points in the subtype of elements of that part’s set, since subtype points with equal values are equal. The enumeration is an equivalence, so it is injective; hence the permuted positions agree. The permutation is also injective, and therefore $a=b$.

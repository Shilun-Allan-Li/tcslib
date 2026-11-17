<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.greedyLargestPartSlice_nonempty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonempty Largest-Part Slice

**Claim.** If $r>0$ and the finite vertex set $R$ is nonempty, then its slice in a part of maximum slice size is nonempty.

**Proof.** Choose a vertex of $R$. Its part slice contains that vertex, so the slice has positive cardinality. The chosen largest part has slice cardinality at least as large as that of this particular part (`remainingPartSlice_card_le_greedyLargestPart`). Its slice therefore also has positive cardinality, and hence is nonempty.

**Key facts.** `FABL.remainingPartSlice_card_le_greedyLargestPart`.

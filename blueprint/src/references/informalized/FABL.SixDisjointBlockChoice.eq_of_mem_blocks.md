<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.SixDisjointBlockChoice.eq_of_mem_blocks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of a block containing an element

**Claim.** If an element belongs to the blocks indexed by $i$ and $j$, then $i=j$.

**Proof.** Suppose the indices were distinct. Pairwise disjointness of the chosen blocks (`SixDisjointBlockChoice.block_pairwiseDisjoint`) would then make the two blocks disjoint. But the element lies in both, contradicting disjointness. Hence the indices agree.

**Key facts.** `FABL.SixDisjointBlockChoice.block_pairwiseDisjoint`.

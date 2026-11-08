<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.LevelKParityTuple.exists_compatible_matching -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compatible perfect matching

**Claim.** There is a perfect matching in the complete multipartite graph such that each matching edge has endpoints with the same assigned label.

**Proof.** Apply the general matching criterion to the assigned labeling. Within every part the labeling is injective, and each label has an even number of preimages among all vertices. The criterion says that these two conditions ensure a perfect matching compatible with the labeling. It yields the required perfect matching directly.

**Key facts.** `FABL.LevelKParityTuple.assignedVertexLabel_injective_on_part`, `FABL.LevelKParityTuple.assignedVertexLabel_even_fiber`, `FABL.exists_graphPartitePerfectMatching_compatible`.

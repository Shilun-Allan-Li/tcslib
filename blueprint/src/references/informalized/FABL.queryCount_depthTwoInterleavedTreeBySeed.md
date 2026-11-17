<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.queryCount_depthTwoInterleavedTreeBySeed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seeded interleaved tree query count

**Claim.** For a seed of four indices in \(\{0,1,2\}\) and an input \(x\in\{−1,1\}^{9}\), the seeded interleaved decision tree makes exactly its prescribed interleaved model cost number of queries.

**Proof.** Expand the seeded tree and its cost using the definitions. The seed selects an ordered triple of distinct blocks, together with the corresponding seed for each block. The ordered query-count theorem then identifies the tree's query count with the ordered model cost for precisely these blocks, seeds, and input.

**Key facts.** `FABL.queryCount_depthTwoInterleavedTreeOrdered`.

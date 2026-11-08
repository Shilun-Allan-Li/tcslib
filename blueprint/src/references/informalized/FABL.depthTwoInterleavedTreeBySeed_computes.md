<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.depthTwoInterleavedTreeBySeed_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness for each seed

**Claim.** For every choice of four indices in $\{0,1,2\}$, the associated decision tree on nine sign-valued coordinates computes the recursive three-way majority function of depth two.

**Proof.** The seeded tree is the ordered interleaved tree with its first three block positions and three leaf seeds determined by the given seed tuple. Apply the correctness theorem for the ordered construction with those choices: it computes recursive three-way majority of depth two. This proves the claim for every seed tuple.

**Key facts.** `FABL.depthTwoInterleavedTreeOrdered_computes`.

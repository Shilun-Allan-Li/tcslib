<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.queryCount_orderedMajorityThreeTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ordered majority tree query count

**Claim.** The ordered majority tree's query count is the first tree's count plus the second tree's count, with the third tree's count added exactly when the first two trees output different signs.

**Proof.** The disjoint-tree composition rule gives the total as the first tree's query count plus the query count of the continuation selected by its output. Applying the same rule to the second tree adds its count and leaves the majority continuation. That continuation contributes zero when the first and second outputs agree, and otherwise contributes the third tree's count. Combining the terms yields the stated formula.

**Key facts.** `FABL.FiniteDecisionTree.queryCount_thenOnDisjoint`, `FABL.queryCount_majorityThreeContinuationTree`.

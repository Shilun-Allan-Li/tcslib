<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.queryCount_orderedNandTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ordered NAND tree query count

**Claim.** For disjoint coordinate sets, the ordered NAND tree makes the first tree's number of queries, plus zero if the first tree outputs \(1\), or the second tree's number if the first tree outputs \(-1\).

**Proof.** By the disjoint-tree composition rule, the total count is the first tree's count plus the count of the NAND continuation selected by the first tree's output. The continuation-count rule says that this contribution is zero when that output is \(1\), and otherwise is the second tree's query count. Substitution gives the claimed expression.

**Key facts.** `FABL.FiniteDecisionTree.queryCount_thenOnDisjoint`, `FABL.queryCount_nandContinuationTree`.

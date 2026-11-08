<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.FiniteDecisionTree.queryCount_mapOutput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relabeling Leaves Preserves Query Count

**Claim.** Replacing every leaf label of a finite decision tree by its image under $g$ does not change the number of queries made on any input.

**Proof.** The query count is the length of the query trace. Relabeling leaves does not alter the trace: at each query, the same coordinate is queried and the same input value selects the corresponding relabeled child; at a leaf, the trace is empty. Thus the query traces agree (`queryTrace_mapOutput`), and consequently their lengths, hence query counts, agree.

**Key facts.** `FABL.FiniteDecisionTree.queryTrace_mapOutput`.

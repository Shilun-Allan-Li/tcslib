<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.FiniteDecisionTree.biasedQueryScore_query -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Biased Query Score at a Query Node

**Claim.** At a query node, the biased query score is the standardized biased value at the queried coordinate plus the score of the selected child.

**Proof.** The query trace of the tree begins with the queried coordinate, followed by the trace of the child selected by the input's value at that coordinate. Passing from this list to its set of coordinates therefore adds the queried coordinate to the child's queried-coordinate set. This coordinate cannot already occur in the child's trace: the child has the queried coordinate removed from its available set, and a tree cannot query a coordinate outside its available set (`FABL.FiniteDecisionTree.not_queries_of_not_mem_available`). Thus the sum defining the score splits into the contribution of the queried coordinate, namely its standardized biased value, and the sum defining the selected child's score.

**Key facts.** `FABL.FiniteDecisionTree.not_queries_of_not_mem_available`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.FiniteDecisionTree.queries_replaceCoordinate_of_not_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Queries ignore unavailable coordinates

**Claim.** Replacing coordinate $j$ by any value leaves unchanged whether coordinate $i$ appears in the tree’s query trace, provided $j$ is not available to the tree.

**Proof.** The query trace depends only on the input values at available coordinates: inputs agreeing there give identical traces (\texttt{queryTrace_eq_of_agreeOn}). Since $j$ is not in the available set, no available coordinate equals $j$. Replacing coordinate $j$ therefore leaves every available input value unchanged, so the two traces agree and have the same membership status for $i$.

**Key facts.** `FABL.FiniteDecisionTree.queryTrace_eq_of_agreeOn`.

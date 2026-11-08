<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.decisionTreeSize_le_of_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Minimality of decision tree size

**Claim.** For a function $f$ and any decision tree $T$ computing it, the minimum number of leaves among trees computing $f$ is at most the number of leaves of $T$.

**Proof.** The existence theorem for a computing tree with a specified leaf count (`FABL.F₂DecisionTree.exists_computingTree_with_size`) supplies a witness showing that the set of possible leaf counts is nonempty. By definition, `decisionTreeSize` is the least such count. Since $T$ computes $f$, its leaf count is one of the possible counts; therefore the least possible count is at most $T$’s leaf count.

**Key facts.** `FABL.F₂DecisionTree.exists_computingTree_with_size`.

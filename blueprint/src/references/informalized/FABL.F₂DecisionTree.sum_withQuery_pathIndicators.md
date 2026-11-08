<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.sum_withQuery_pathIndicators -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicators After Extending Paths

**Claim.** When a fresh coordinate is assigned branch value $b$ on every path in a list, the sum of output-weighted cylinder indicators at $x$ equals the original sum if $x_i=b$, and equals zero otherwise.

**Proof.** Split according to whether $x_i=b$. The output of each path is unchanged by extending it at coordinate $i$ (`FABL.F₂DecisionTree.Path.withQuery_output`). Because $i$ is absent from each path’s support, its extended indicator equals the original indicator when $x_i=b$, and equals zero otherwise (`FABL.F₂DecisionTree.Path.indicator_withQuery`). In the first case, each summand is therefore unchanged, so the sums agree. In the second case every extended summand vanishes, so the sum is zero.

**Key facts.** `FABL.F₂DecisionTree.Path.withQuery_output`, `FABL.F₂DecisionTree.Path.indicator_withQuery`.

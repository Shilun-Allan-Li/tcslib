<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.longPathIndicatorSum_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of the Long-Path Indicator Sum

**Claim.** For any finite list of paths and any input, the sum of the indicators of paths whose length exceeds $k$ is nonnegative.

**Proof.** The sum is a finite sum of terms, one for each path, equal to its indicator when its length exceeds $k$ and zero otherwise. Each indicator is nonnegative (`FABL.F₂DecisionTree.Path.indicator_nonneg`), and zero is nonnegative as well. Therefore every summand is nonnegative, so the whole sum is nonnegative.

**Key facts.** `FABL.F₂DecisionTree.Path.indicator_nonneg`.

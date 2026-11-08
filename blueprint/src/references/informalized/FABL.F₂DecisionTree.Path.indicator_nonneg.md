<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.Path.indicator_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of the path indicator

**Claim.** For any point of the binary cube, the indicator of the points matching a given path is nonnegative.

**Proof.** Split according to whether the point matches the path. If it does, the path indicator equals $1$ by the indicator-on-matches fact (`indicator_eq_one_of_matches`), so it is nonnegative. If it does not, the indicator equals $0$ by the indicator-on-nonmatches fact (`indicator_eq_zero_of_not_matches`), which is also nonnegative.

**Key facts.** `FABL.F₂DecisionTree.Path.indicator_eq_one_of_matches`, `FABL.F₂DecisionTree.Path.indicator_eq_zero_of_not_matches`.

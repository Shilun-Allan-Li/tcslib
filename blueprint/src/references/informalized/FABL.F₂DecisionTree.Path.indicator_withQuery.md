<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.Path.indicator_withQuery -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator after adding a query

**Claim.** After adding the requirement that coordinate $i$ equal $b$, the path indicator at $x$ equals its original value when $x_i=b$, and is zero otherwise.

**Proof.** There are two possibilities for whether $x$ matches the original path, and two for whether $x_i=b$. The matching characterization for an added query (`matches_withQuery_iff`) says that $x$ matches the extended path exactly when both conditions hold. If both hold, the original and extended indicators are each $1$, by the indicator-on-matches fact (`indicator_eq_one_of_matches`). If $x_i\ne b$, the extended path is not matched, so its indicator is $0$; this agrees with the right-hand side of the claimed formula. If $x_i=b$ but $x$ does not match the original path, the extended path is also not matched, and both sides are again zero, using the indicator-on-nonmatches fact (`indicator_eq_zero_of_not_matches`).

**Key facts.** `FABL.F₂DecisionTree.Path.indicator_eq_one_of_matches`, `FABL.F₂DecisionTree.Path.matches_withQuery_iff`, `FABL.F₂DecisionTree.Path.indicator_eq_zero_of_not_matches`.

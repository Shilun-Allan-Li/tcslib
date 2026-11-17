<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.one_le_longPathIndicatorSum_of_mem_of_matches -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matched Long Path Contribution

**Claim.** If a path in the list has length greater than $k$ and its assignments match $x$, then the long-path indicator sum at $x$ is at least $1$.

**Proof.** Induct on the list. The empty list cannot contain the given path. For a nonempty list, separate the head path from the tail. If the head is the given path, its length exceeds $k$, and matching makes its indicator equal to $1$ (`FABL.F₂DecisionTree.Path.indicator_eq_one_of_matches`). The tail contributes a nonnegative sum (`FABL.F₂DecisionTree.longPathIndicatorSum_nonneg`), so the whole sum is at least $1$. Otherwise the given path occurs in the tail, and induction says the tail sum is at least $1$. The head contributes either zero or a nonnegative indicator (`FABL.F₂DecisionTree.Path.indicator_nonneg`), so adding it preserves that lower bound.

**Key facts.** `FABL.F₂DecisionTree.Path.indicator_eq_one_of_matches`, `FABL.F₂DecisionTree.longPathIndicatorSum_nonneg`, `FABL.F₂DecisionTree.Path.indicator_nonneg`.

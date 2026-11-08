<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.randomizedDecisionTreeComplexity_recursiveNAND_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive NAND Complexity Bound

**Claim.** For every depth $d$, the randomized decision-tree complexity of recursive NAND is at most $(2/\rho)\rho^d$, where $\rho=(1+\sqrt{33})/4$.

**Proof.** For each depth $d$, the constructed recursive NAND randomized tree computes the function. Nonnegativity of every worst-case cost ensures that the set defining the complexity is bounded below. Its infimum is consequently at most the worst-case cost of this particular tree. That cost is at most $(2/\rho)\rho^d$ (\texttt{recursiveNandRandomizedTree\_worstCaseCost\_le\_growth}), giving the claimed inequality.

**Key facts.** `FABL.RandomizedDecisionTree.worstCaseCost_nonneg`, `FABL.recursiveNandRandomizedTree_worstCaseCost_le_growth`.

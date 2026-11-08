<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.recursiveNandRandomizedTree_worstCaseCost_le_growth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Worst-Case Cost Growth Bound

**Claim.** For every $d\in\mathbb{N}$, the worst-case expected query cost of the level-$d$ randomized tree is at most $\frac{2}{\rho}\rho^d$, where $\rho=(1+\sqrt{33})/4$.

**Proof.** The worst-case expected cost is at most the larger of the two recurrence costs, the false-output and true-output costs (\(\texttt{FABL.recursiveNandRandomizedTree_worstCaseCost_le_recurrence}\)). That maximum is bounded by $\frac{2}{\rho}\rho^d$ (\(\texttt{FABL.recursiveNand_maxCost_le}\)). Combining the inequalities proves the claimed growth bound.

**Key facts.** `FABL.recursiveNandRandomizedTree_worstCaseCost_le_recurrence`, `FABL.recursiveNand_maxCost_le`.

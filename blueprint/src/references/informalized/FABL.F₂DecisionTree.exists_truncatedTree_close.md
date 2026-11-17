<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.exists_truncatedTree_close -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shallow Approximation by Truncation

**Claim.** For any positive error tolerance and fallback label, a tree has a truncation whose depth is at most the specified truncation degree and whose evaluation differs from the original on at most the prescribed fraction of inputs.

**Proof.** Choose the truncation of $T$ at depth $k=\mathrm{decisionTreeTruncationDegree}(\mathrm{leafCount}(T),\varepsilon)$, using the given fallback label. The depth bound follows from the theorem that truncation at depth $k$ has depth at most $k$ (`FABL.F₂DecisionTree.depth_truncate_le`). The relative Hamming distance bound for this particular truncation is supplied by `FABL.F₂DecisionTree.relativeHammingDist_eval_truncate_decisionTreeTruncationDegree_le`, whose positivity hypothesis is exactly the assumed $\varepsilon>0$. Together these give the required tree and both estimates.

**Key facts.** `FABL.F₂DecisionTree.depth_truncate_le`, `FABL.F₂DecisionTree.relativeHammingDist_eval_truncate_decisionTreeTruncationDegree_le`.

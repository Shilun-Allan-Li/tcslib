<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.vectorFourierWeightAbove_decisionTreeTruncationDegree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decision-tree Fourier concentration

**Claim.** If a sign-valued function is computed by a decision tree with $s$ leaves, then for every $0<\epsilon\le 1$, its Fourier weight above the truncation degree $\lceil\log_2(s/\epsilon)\rceil$ is at most $\epsilon$.

**Proof.** Let $k$ be the decision-tree truncation degree for $s=T.\mathrm{leafCount}$ and the given $\epsilon$. The tail estimate for a sign-valued decision tree bounds its Fourier weight above any degree $k$ by $s\,2^{-k}$ (\texttt{vectorFourierWeightAbove\_eval\_le\_leafCount\_mul\_inverseTwoPow}). The leaf count is positive (\texttt{leafCount\_pos}), and $\epsilon>0$ by hypothesis. The defining truncation degree is large enough that $s\,2^{-k}\le\epsilon$ (\texttt{mul\_inverseTwoPow\_decisionTreeTruncationDegree\_le}). Combining these two bounds proves the claim.

**Key facts.** `FABL.F₂DecisionTree.vectorFourierWeightAbove_eval_le_leafCount_mul_inverseTwoPow`, `FABL.F₂DecisionTree.leafCount_pos`, `FABL.F₂DecisionTree.mul_inverseTwoPow_decisionTreeTruncationDegree_le`.

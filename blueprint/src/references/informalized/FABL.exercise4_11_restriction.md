<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.exercise4_11_restriction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier One-Norm Under Restriction

**Claim.** For the restriction of a Boolean function obtained by fixing the coordinates outside $J$, its Fourier one-norm is at most $2$ raised to the depth of the restricted decision tree.

**Proof.** Choose a decision tree computing the restricted binary function whose depth is its decision-tree depth (`F₂DecisionTree.exists_computingTree_depth_eq_decisionTreeDepth`). Map each leaf value through the real sign-value map. The resulting real-valued tree computes the restriction expressed on the sign cube: this follows from the pointwise evaluation identity for mapped trees (`F₂DecisionTree.eval_mapOutputs`) and the computation characterization (`F₂DecisionTree.computes_iff`).

The decision-tree spectral bound (`F₂DecisionTree.spectralPNorm_one_le_infinityNorm_mul_two_pow_depth_of_computes`) bounds the spectral one-norm by the function's infinity norm times $2$ to the tree depth. The Fourier one-norm equals this spectral one-norm after identifying the binary and sign cubes (`fourierOneNorm_eq_spectralPNorm_one`). Every output is a sign, so its real value is either $-1$ or $1$ (`signValue_eq_neg_one_or_one`); hence the infinity norm is $1$. Finally, mapping the tree's outputs does not change its depth (`F₂DecisionTree.depth_mapOutputs`), and the chosen tree's depth is the restricted decision-tree depth. Substitution yields the claimed bound.

**Key facts.** `FABL.F₂DecisionTree.exists_computingTree_depth_eq_decisionTreeDepth`, `FABL.F₂DecisionTree.eval_mapOutputs`, `FABL.F₂DecisionTree.computes_iff`, `FABL.F₂DecisionTree.spectralPNorm_one_le_infinityNorm_mul_two_pow_depth_of_computes`, `FABL.fourierOneNorm_eq_spectralPNorm_one`, `FABL.signValue_eq_neg_one_or_one`, `FABL.F₂DecisionTree.depth_mapOutputs`.

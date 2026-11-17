<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.spectralSparsity_pathExpansion_le_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sparsity of a Path Expansion

**Claim.** The spectral sparsity of a path expansion is at most the sum, over its paths, of two raised to each path’s length.

**Proof.** Proceed by induction on the path list. The empty expansion is zero, so all its Fourier coefficients vanish and its spectral sparsity is zero. For a list beginning with a path $p$, the expansion is the sum of the function $x\mapsto p.output\,p.indicator(x)$ and the expansion from the remaining list (the path expansion decomposition, `FABL.F₂DecisionTree.pathExpansion_cons`). Spectral sparsity of a sum is at most the sum of the two spectral sparsities (`FABL.spectralSparsity_add_le`). Multiplication by a constant cannot increase spectral sparsity (`FABL.spectralSparsity_const_mul_le`), and the spectral sparsity of a path indicator is exactly $2^{length(p)}$ (`FABL.F₂DecisionTree.Path.spectralSparsity_indicator`). Combining these with the induction hypothesis gives the desired bound; the resulting two terms are precisely the sum indexed by the original list.

**Key facts.** `FABL.F₂DecisionTree.pathExpansion_cons`, `FABL.spectralSparsity_add_le`, `FABL.spectralSparsity_const_mul_le`, `FABL.F₂DecisionTree.Path.spectralSparsity_indicator`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.sum_abs_pathOutput_le_leafCount_mul_infinityNorm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leaf Output Bound

**Claim.** If a real-valued decision tree computes $f$, the sum of the absolute values of its path outputs is at most its number of leaves times the maximum of $|f(x)|$ over all inputs.

**Proof.** Every path in the tree’s path list has output bounded in absolute value by the infinity norm of $f$ (`FABL.F₂DecisionTree.abs_path_output_le_binaryFunctionInfinityNorm`), because the tree computes $f$. A list of $m$ real weights, each at most $B$, has sum at most $mB$ (`FABL.F₂DecisionTree.sum_map_le_length_mul`). Apply this with the path outputs’ absolute values and the infinity norm as the common bound. The number of paths equals the number of leaves (`FABL.F₂DecisionTree.length_paths_eq_leafCount`), giving the claimed inequality.

**Key facts.** `FABL.F₂DecisionTree.length_paths_eq_leafCount`, `FABL.F₂DecisionTree.sum_map_le_length_mul`, `FABL.F₂DecisionTree.abs_path_output_le_binaryFunctionInfinityNorm`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.abs_path_output_le_binaryFunctionInfinityNorm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Path output bounded by function norm

**Claim.** If a real-valued decision tree computes $f$ and a path occurs in the tree's path list, then the absolute value of that path's output is at most the supremum of $|f|$ over all inputs.

**Proof.** Evaluate $f$ at the path's base input. Every coordinate fixed along the path agrees with that input (`FABL.F₂DecisionTree.Path.matches_base`). Since the path occurs in the path list and the tree computes $f$, the agreement of the input with the path forces $f$ at that input to equal the path's output (`FABL.F₂DecisionTree.computes_eq_path_output_of_matches`). Hence the absolute value of the path output equals the absolute value of $f$ at the base input. The latter is bounded by the binary function infinity norm, which bounds $|f|$ at every input (`FABL.abs_le_binaryFunctionInfinityNorm`).

**Key facts.** `FABL.F₂DecisionTree.Path.matches_base`, `FABL.F₂DecisionTree.computes_eq_path_output_of_matches`, `FABL.abs_le_binaryFunctionInfinityNorm`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.decisionTreeDepth_binaryBooleanDual_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Sided Depth Bound Under Boolean Duality

**Claim.** The minimum depth of a binary decision tree computing the Boolean dual of $f$ is at most the minimum depth of a binary decision tree computing $f$.

**Proof.** Choose a tree computing $f$ whose depth is the minimum possible (\texttt{exists_computingTree_depth_eq_decisionTreeDepth}). Transform it by complementing every queried input and negating every output. For any input $x$, the transformed tree evaluates to the negation of the original tree on the coordinatewise complement of $x$: this follows from the evaluation rules for output maps and complemented inputs (\texttt{F₂DecisionTree.eval_mapOutputs}, \texttt{F₂DecisionTree.eval_complementInputs}). Since the original tree computes $f$, the transformed tree therefore computes $f^*$. These transformations preserve depth, so the transformed tree has the same depth as the chosen tree. The minimum depth of a function is no greater than the depth of any tree computing it (\texttt{F₂DecisionTree.decisionTreeDepth_le_of_computes}); applying this to the transformed tree proves the inequality.

**Key facts.** `FABL.F₂DecisionTree.exists_computingTree_depth_eq_decisionTreeDepth`, `FABL.F₂DecisionTree.eval_mapOutputs`, `FABL.F₂DecisionTree.eval_complementInputs`, `FABL.F₂DecisionTree.computes_iff`, `FABL.F₂DecisionTree.decisionTreeDepth_le_of_computes`.

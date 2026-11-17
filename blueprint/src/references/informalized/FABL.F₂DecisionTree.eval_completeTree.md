<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.eval_completeTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Complete Tree

**Claim.** The complete decision tree constructed from a function $f$ evaluates to $f$ on every input.

**Proof.** Fix an input $x$ and apply the evaluation property of the partial complete tree (`FABL.F₂DecisionTree.eval_completeTreeAux`) with initial partial input the zero vector and all coordinates available. Its agreement hypothesis holds vacuously because no coordinate lies outside the full coordinate set. The property gives that evaluation at $x$ is $f(x)$; since this initial partial tree is the complete tree, the desired equality follows pointwise, hence as functions.

**Key facts.** `FABL.F₂DecisionTree.eval_completeTreeAux`.

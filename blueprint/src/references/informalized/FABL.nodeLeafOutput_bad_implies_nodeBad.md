<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.nodeLeafOutput_bad_implies_nodeBad -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bad Output Forces a Bad Decision

**Claim.** If the leaf output associated to a node decision fails to compute the target on inputs matching the fixed signs, then the node decision is bad.

**Proof.** Suppose, toward a contradiction, that the decision is not bad. If the decision is missing, the definition makes it bad, so this case is impossible. Thus it is present and correct, by the fact that a present decision which is not bad is correct (`JuntaNodeDecision.isCorrect_of_not_isBad`). Since the target depends on $J$ and $|J\setminus P|\le 0$, every correct decision must be constant: there is a sign value for which the decision is that constant (`exists_constant_of_correctNode_of_card_sdiff_le_zero`). Its associated output is therefore the leaf carrying that value. A constant restriction is computed by this leaf on every matching input (`F₂DecisionTree.computesJuntaRestriction_leaf`), contradicting the assumed badness of the output. Thus the decision is bad.

**Key facts.** `FABL.JuntaNodeDecision.isCorrect_of_not_isBad`, `FABL.exists_constant_of_correctNode_of_card_sdiff_le_zero`, `FABL.F₂DecisionTree.computesJuntaRestriction_leaf`.

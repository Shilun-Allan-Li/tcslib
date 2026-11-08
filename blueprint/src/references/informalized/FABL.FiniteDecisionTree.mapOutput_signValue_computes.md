<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.FiniteDecisionTree.mapOutput_signValue_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Relabeling Preserves Computation

**Claim.** If a decision tree with sign outputs computes a Boolean function, then replacing each output sign by its real value gives a tree computing the real-valued version of that function.

**Proof.** Fix an input $x$. Relabeling the leaves by a map $g$ changes the tree's evaluation to $g$ applied to its original evaluation (`eval_mapOutput`). Since the original tree computes the target, its evaluation at $x$ is the target value there. Taking $g$ to be the sign-to-real map gives exactly the real-valued target at $x$. As this holds for every input, the relabeled tree computes that function.

**Key facts.** `FABL.FiniteDecisionTree.eval_mapOutput`.

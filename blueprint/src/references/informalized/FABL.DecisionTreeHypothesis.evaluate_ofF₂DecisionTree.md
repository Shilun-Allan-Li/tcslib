<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DecisionTreeHypotheses.lean :: FABL.DecisionTreeHypothesis.evaluate_ofF₂DecisionTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation on the Sign Cube

**Claim.** For a finite-coordinate decision tree with sign-valued leaves, its associated Boolean function at a sign vector equals the original tree’s evaluation on the binary vector corresponding to that sign vector.

**Proof.** Fix a sign vector $x$. By definition, the associated Boolean function evaluates the converted tree at the binary vector obtained by applying the inverse binary-to-sign correspondence coordinatewise to $x$. The evaluation-preservation result (`eval_ofF₂DecisionTree`) says that the converted tree’s value at any binary input equals the original tree’s value there. Applying it to this particular input gives the claimed equality at $x$, and hence equality of the functions.

**Key facts.** `FABL.DecisionTreeHypothesis.eval_ofF₂DecisionTree`.

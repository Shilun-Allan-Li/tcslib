<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.F₂LinearEquation.eval_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation preserves equation addition

**Claim.** Evaluating the sum of two linear equations at an assignment gives the sum of their evaluations.

**Proof.** At each coordinate, the coefficient of the sum equation is the sum of the two coefficients. Multiplying by the assignment value distributes over this sum. Summing over all coordinates and using additivity of finite sums gives the sum of the two evaluations.

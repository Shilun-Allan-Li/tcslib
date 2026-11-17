<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/LinearCSPAlgorithms.lean :: FABL.CSPConstraint.eval_toF₂LinearEquation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Associated Linear Equation

**Claim.** For any assignment to the variables, the associated linear equation evaluates to the sum of the assigned values on the constraint’s ordered scope.

**Proof.** Unfold the equation evaluation and the associated equation. Each variable’s coefficient is the indicator of whether it lies in the image of the constraint scope, so the sum over all variables reduces to the sum over that image. The scope is injective, hence summing over its image is the same as summing over scope positions, with each position counted exactly once. This yields the sum of the assigned values along the ordered scope.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/LaplacianAndPoincare.lean :: FABL.norm_discreteGradient_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared Norm of the Discrete Gradient

**Claim.** For every function on the Boolean cube and every input, the squared Euclidean norm of its discrete gradient is the sum of the squares of its coordinate derivatives.

**Proof.** The discrete gradient is a function on the finite coordinate set, viewed with the $L^2$ norm. Its squared norm is therefore the sum of the squares of the absolute values of its coordinates. Each coordinate derivative is real, so its absolute value squared equals its square. This gives the stated identity.

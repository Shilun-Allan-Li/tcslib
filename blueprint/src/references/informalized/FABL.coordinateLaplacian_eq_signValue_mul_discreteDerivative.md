<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/DiscreteDerivatives.lean :: FABL.coordinateLaplacian_eq_signValue_mul_discreteDerivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Laplacian and Discrete Derivative

**Claim.** The coordinate Laplacian equals the sign value of the selected coordinate times the discrete derivative.

**Proof.** The coordinate Laplacian is $f(x)$ minus the coordinate expectation (`FABL.coordinateLaplacian_apply`). The identity decomposing $f(x)$ as the sign value at coordinate $i$ times the discrete derivative, plus the coordinate expectation, then gives the result by subtraction (`FABL.eq_signValue_mul_discreteDerivative_add_coordinateExpectation`).

**Key facts.** `FABL.coordinateLaplacian_apply`, `FABL.eq_signValue_mul_discreteDerivative_add_coordinateExpectation`.

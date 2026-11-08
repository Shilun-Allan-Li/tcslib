<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.productCoordinateLaplacian_uniformSign_eq_coordinateLaplacian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform-sign coordinate Laplacian

**Claim.** For the uniform sign distribution, the product coordinate Laplacian agrees with the coordinate Laplacian on the Boolean cube.

**Proof.** Unfold both Laplacians. Each is the function minus an averaging operator: the product version subtracts the coordinate projection, and the Boolean-cube version subtracts coordinate expectation. For the uniform sign law, these averaging operators agree (`coordinateProjection_uniformSign_eq_coordinateExpectation`), so their differences agree as well.

**Key facts.** `FABL.coordinateProjection_uniformSign_eq_coordinateExpectation`.

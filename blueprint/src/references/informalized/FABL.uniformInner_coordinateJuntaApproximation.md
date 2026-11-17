<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.uniformInner_coordinateJuntaApproximation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Junta approximation inner product identity

**Claim.** The uniform inner product of $f$ with its sign-thresholded coordinate projection onto $J$ equals the uniform inner product of that projection with the same thresholded function.

**Proof.** Write $g$ for the sign-thresholded coordinate projection. It depends only on coordinates in $J$ (`coordinateJuntaApproximation_dependsOnly`), so projecting $g$ onto those coordinates leaves it unchanged (`projectOnCoordinates_eq_self_of_dependsOnly`). The coordinate projection is self-adjoint: the inner product of $f$ with the projection of $g$ equals the inner product of the projection of $f$ with $g$ (`projectOnCoordinates_selfAdjoint`). Substituting that the projection of $g$ is $g$ gives the desired equality in product inner products. Finally, the product inner product for the uniform sign distribution agrees with the uniform inner product (`productInner_uniformSign`), yielding the stated identity.

**Key facts.** `FABL.coordinateJuntaApproximation_dependsOnly`, `FABL.projectOnCoordinates_eq_self_of_dependsOnly`, `FABL.projectOnCoordinates_selfAdjoint`, `FABL.productInner_uniformSign`.

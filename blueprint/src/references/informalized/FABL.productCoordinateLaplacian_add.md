<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.productCoordinateLaplacian_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of the coordinate Laplacian

**Claim.** The product coordinate Laplacian applied to $f+g$ equals the sum of its applications to $f$ and $g$.

**Proof.** Write the coordinate Laplacian as the identity operator minus the coordinate projection. The coordinate projection is additive (`projectOnCoordinates_add`), so applying the Laplacian to $f+g$ gives $(f+g)-(P f+P g)$, where $P$ is that projection. Rearranging by the module laws gives $(f-Pf)+(g-Pg)$, which is the sum of the two Laplacians.

**Key facts.** `FABL.projectOnCoordinates_add`.

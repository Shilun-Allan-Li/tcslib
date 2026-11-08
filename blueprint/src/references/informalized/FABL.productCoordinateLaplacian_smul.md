<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.productCoordinateLaplacian_smul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneity of the coordinate Laplacian

**Claim.** For every coordinate $i$ and scalar $c$, the product coordinate Laplacian of $cf$ is $c$ times the product coordinate Laplacian of $f$.

**Proof.** By definition, the product coordinate Laplacian subtracts the coordinate projection from the function. The coordinate projection is linear in the function: projecting $cf$ gives $c$ times the projection of $f$ (`projectOnCoordinates_smul`). Thus the difference $cf-c\,\mathrm{proj}_i(f)$ factors as $c(f-\mathrm{proj}_i(f))$, as claimed.

**Key facts.** `FABL.projectOnCoordinates_smul`.

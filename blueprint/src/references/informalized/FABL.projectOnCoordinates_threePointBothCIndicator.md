<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.projectOnCoordinates_threePointBothCIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Projection of a Three-Point Indicator

**Claim.** For the indicator that both coordinates equal $c$, projection onto $J$ under the uniform product law on the three-point space gives the product of the fixed-coordinate indicator and the value $1/3$ for each averaged coordinate.

**Proof.** Fix an input $x$. At each coordinate, merging $x$ with the sampled point keeps $x_i$ when $i\in J$ and uses the sampled value $y_i$ otherwise. Consequently, the indicator being averaged factors as a product over coordinates: its $i$th factor is the indicator that $x_i=c$ when $i\in J$, and the indicator that $y_i=c$ otherwise. The expectation of a product of coordinate functions under an independent product distribution factors into the product of their individual expectations (the product-expectation formula for independent coordinates, `FABL.pmfExpectation_independentProductPMF_prod`). A fixed-coordinate factor has expectation equal to its constant value (`FABL.pmfExpectation_const`); for a uniformly sampled three-point coordinate, the indicator of $c$ has expectation $1/3$ (`FABL.pmfExpectation_threePointCIndicator`). Combining these factors yields the stated product.

**Key facts.** `FABL.pmfExpectation_independentProductPMF_prod`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_threePointCIndicator`.

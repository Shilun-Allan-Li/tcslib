<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.projectOnCoordinates_productFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Projection of a product basis function

**Claim.** Projecting a product basis function onto coordinates $J$ leaves it unchanged when its support is contained in $J$, and gives zero otherwise.

**Proof.** Fix an input $x$. In the expectation defining the projection, the product basis function evaluated on the merged input factors into a product over coordinates: on $J$ the factor is evaluated at $x$, and off $J$ it is averaged over an independent coordinate with law $\pi$. The product expectation factors into the product of these one-coordinate expectations (pmfExpectation_independentProductPMF_prod). On coordinates in $J$, the factors are unchanged; off $J$, the expected basis function is zero unless its index is the constant-one index, in which case the expectation is one (expect_basis). If the support is contained in $J$, every factor off $J$ is therefore one, so the product is the original product basis function; the support-containment criterion says exactly that all indices off $J$ are zeroIndex (multiIndexSupport_subset_iff). If support is not contained in $J$, some coordinate outside $J$ has a nonzero index, and its averaged factor is zero. The whole product, and hence the projection at $x$, is zero. Since this holds for every $x$, the function identity follows.

**Key facts.** `FABL.pmfExpectation_independentProductPMF_prod`, `FABL.FiniteFourierBasis.expect_basis`, `FABL.multiIndexSupport_subset_iff`, `FABL.pmfExpectation_const`.

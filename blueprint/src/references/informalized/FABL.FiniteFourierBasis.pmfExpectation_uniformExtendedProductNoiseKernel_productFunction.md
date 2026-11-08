<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedNoiseExtensions.lean :: FABL.FiniteFourierBasis.pmfExpectation_uniformExtendedProductNoiseKernel_productFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Extended Noise on Product Basis Functions

**Claim.** For the uniform product measure and the stated admissible range of $\rho$, the expectation of the product basis function indexed by $a$ under extended product noise at $x$ is $\rho^{d(a)}$ times that function evaluated at $x$.

**Proof.** Independence factors the expectation of the product basis function into the product of the one-coordinate expectations (\(\texttt{FABL.pmfExpectation_independentProductPMF_prod}\)). Each coordinate expectation is $1$ at the distinguished constant index and otherwise is $\rho B_{a_i}(x_i)$ (\(\texttt{FABL.FiniteFourierBasis.pmfExpectation_uniformExtendedCoordinateNoisePMF_basis}\)). Separating scalar and basis factors, the scalar product has one factor of $\rho$ for each nonconstant coordinate and a factor of $1$ for each constant coordinate. Its value is therefore $\rho$ raised to the number of nonconstant coordinates, which is $d(a)$. The remaining factor is the product basis function evaluated at $x$.

**Key facts.** `FABL.pmfExpectation_independentProductPMF_prod`, `FABL.FiniteFourierBasis.pmfExpectation_uniformExtendedCoordinateNoisePMF_basis`.

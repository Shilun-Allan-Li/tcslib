<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.pmfExpectation_productNoiseKernel_productFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Isotropic Noise on Product Basis Functions

**Claim.** Under product noise with common parameter $\rho\in[0,1]$, the expectation of the product basis function indexed by $a$ at $x$ is $\rho^{d(a)}$ times that basis function evaluated at $x$, where $d(a)$ counts the nonconstant coordinates of $a$.

**Proof.** Independence factors the expectation of the product basis function into the product of the one-coordinate expectations (\(\texttt{FABL.pmfExpectation_independentProductPMF_prod}\)). In each coordinate the factor is $1$ for a constant index and otherwise is $\rho B_{a_i}(x_i)$ (\(\texttt{FABL.FiniteFourierBasis.pmfExpectation_productCoordinateNoisePMF_basis}\)). Separate the scalar and basis-function factors across coordinates. The scalar product contributes one factor of $\rho$ for each nonconstant coordinate and $1$ for each constant coordinate; hence it is $\rho$ raised to the cardinality of the support, namely $d(a)$. The remaining product is the product basis function evaluated at $x$.

**Key facts.** `FABL.pmfExpectation_independentProductPMF_prod`, `FABL.FiniteFourierBasis.pmfExpectation_productCoordinateNoisePMF_basis`.

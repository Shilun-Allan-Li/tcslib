<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.FiniteFourierBasis.pmfExpectation_anisotropicProductNoiseKernel_productFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Anisotropic Noise on Product Basis Functions

**Claim.** Under coordinatewise noise with parameter $\rho_i$ in coordinate $i$, the expectation of the product basis function indexed by $a$ at $x$ equals $\left(\prod_i (1\text{ if }a_i=0_B,\text{ else }\rho_i)\right)$ times that basis function evaluated at $x$.

**Proof.** The noisy coordinates are independent, so the expectation of the product of their basis values factors as the product of the one-coordinate expectations (\(\texttt{FABL.pmfExpectation_independentProductPMF_prod}\)). For each coordinate, the one-coordinate noise expectation is $1$ for the constant basis vector and otherwise is $\rho_i B_{a_i}(x_i)$ (\(\texttt{FABL.FiniteFourierBasis.pmfExpectation_productCoordinateNoisePMF_basis}\)). Thus each factor can be written as the product of the indicated scalar and $B_{a_i}(x_i)$; in the constant-index case this uses that the distinguished basis function is identically one. Distributing the product over these two factors separates the coordinate scalars from the product basis function, giving the formula.

**Key facts.** `FABL.pmfExpectation_independentProductPMF_prod`, `FABL.FiniteFourierBasis.pmfExpectation_productCoordinateNoisePMF_basis`.

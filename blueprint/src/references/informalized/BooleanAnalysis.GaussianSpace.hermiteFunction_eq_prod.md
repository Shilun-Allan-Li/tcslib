<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basic.lean :: BooleanAnalysis.GaussianSpace.hermiteFunction_eq_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Formula for Hermite Functions

**Claim.** The multivariate Hermite function at $\alpha$ and $x$ is the product over coordinates of the normalized one-variable Hermite polynomials evaluated at the corresponding coordinates.

**Proof.** The multivariate Hermite polynomial is defined as the product, over coordinates $i$, of the one-variable polynomial for degree $\alpha_i$ with its variable replaced by the coordinate variable $X_i$. Evaluating this product at $x$ sends each factor to the corresponding one-variable polynomial evaluated at $x_i$, since polynomial evaluation preserves products. The resulting product is the stated formula.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/Siegenthaler.lean :: FABL.restrictionFourierCoeff_encoding_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty restricted Fourier coefficient

**Claim.** The empty Fourier coefficient of the restricted real encoding of a Boolean function is one half of one minus the mean of its sign-valued restriction.

**Proof.** The encoding identity (binaryFunctionOnSignCube_booleanRealEmbedding_booleanFunctionF₂Encoding) identifies the function on the sign cube with $x\mapsto (1-f.toReal(x))/2$. In the restricted coefficient, the empty monomial is $1$, so the coefficient is the uniform expectation over the free coordinates of $(1-f.toReal(\operatorname{combine}(y,z)))/2$. Pulling the constant factor $1/2$ outside the expectation and distributing expectation over subtraction gives $(1-\mathbb E_y[f.toReal(\operatorname{combine}(y,z))])/2$. By the definition of restriction and its pointwise evaluation rule (signRestriction_apply), this expectation is the mean of the sign-valued restriction, as claimed.

**Key facts.** `FABL.binaryFunctionOnSignCube_booleanRealEmbedding_booleanFunctionF₂Encoding`, `FABL.signRestriction_apply`.

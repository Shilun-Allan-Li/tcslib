<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/FourierToF₂Polynomial.lean :: FABL.numericalEval_fourierToF₂Coeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of normalized Fourier coefficients

**Claim.** The numerical polynomial whose coefficients are half the difference between the empty-set indicator and the Fourier-substitution coefficients evaluates to $(1-p(\sigma(x)))/2$ on the binary cube.

**Proof.** Fix a binary vector $x$ and expand the numerical evaluation using the definition of the coefficients. Distributing the half-difference through the finite sum separates it into the sum of the empty-set indicator terms divided by two, minus the numerical evaluation of the Fourier-substitution coefficients divided by two. Only the empty set contributes to the first sum, and its numerical monomial is $1$. Thus the result is $(1-\operatorname{numericalEval}(\text{Fourier-substitution coefficients})(x))/2$. The evaluation identity for Fourier-substitution coefficients (`numericalEval_fourierSubstitutionCoeff`) identifies this value with $(1-p(\sigma(x)))/2$, as required.

**Key facts.** `FABL.numericalEval_fourierSubstitutionCoeff`.

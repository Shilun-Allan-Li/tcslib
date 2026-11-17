<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianSharpLevelOneCounterexample.lean :: FABL.fourierCoeff_signedHammingTwoTail_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton Coefficient of a Signed Tail

**Claim.** The singleton Fourier coefficient of the signed two-sided tail equals twice the singleton Fourier coefficient of the upper-tail indicator.

**Proof.** By linearity of the uniform expectation, the coefficient of the difference defining the signed tail is the upper-tail coefficient minus the coefficient of the function obtained by evaluating the upper-tail indicator at the negated input. Negating the input reverses the sign of a singleton character, so that latter coefficient is the negative of the original upper-tail coefficient (`fourierCoeff_comp_neg_singleton`). Substituting this gives the original coefficient minus its negative, which is twice the original coefficient.

**Key facts.** `FABL.fourierCoeff_comp_neg_singleton`.

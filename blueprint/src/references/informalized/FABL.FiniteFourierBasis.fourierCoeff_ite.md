<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.fourierCoeff_ite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficient of a piecewise function

**Claim.** The Fourier coefficient of the function equal to $f$ when $P$ holds and to $g$ otherwise is the corresponding piecewise choice between their Fourier coefficients.

**Proof.** Split into the two possibilities for $P$. If $P$ holds, the piecewise function is $f$ and the claimed coefficient is the coefficient of $f$. If $P$ does not hold, it is $g$ and the claimed coefficient is the coefficient of $g$.

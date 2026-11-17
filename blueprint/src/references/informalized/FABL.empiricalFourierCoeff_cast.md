<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FourierEstimation.lean :: FABL.empiricalFourierCoeff_cast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of Empirical Fourier Coefficients

**Claim.** For samples labeled by the values of a Boolean function, the rational empirical Fourier coefficient, viewed as a real number, equals the real empirical Fourier coefficient on the same inputs.

**Proof.** For each input $x_i$, the rational observation formed from the label $f(x_i)$ becomes, after casting to the reals, the real Fourier observation of $f$ at $x_i$; this is exactly the observation-cast identity (`rationalFourierObservation_cast`). Summing these equalities over all sample indices preserves equality, and casting the rational average to the reals agrees with taking the real average. The resulting expression is the defining sum for the real empirical Fourier coefficient.

**Key facts.** `FABL.rationalFourierObservation_cast`.

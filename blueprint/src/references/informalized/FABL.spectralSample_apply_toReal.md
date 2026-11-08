<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BasicFourierFormulas.lean :: FABL.spectralSample_apply_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Point probabilities of the spectral sample

**Claim.** For a Boolean-valued function $f$ and any coordinate subset $S$, the real-valued probability assigned by its spectral sample to $S$ equals the squared Fourier coefficient of the real-valued version of $f$ at $S$.

**Proof.** By definition, the spectral sample assigns mass obtained by taking the nonnegative real part of the Fourier weight, which here is the square of the Fourier coefficient. Since a square is nonnegative, converting this mass from its extended nonnegative representation back to a real number returns the original Fourier weight. This is exactly the stated identity.

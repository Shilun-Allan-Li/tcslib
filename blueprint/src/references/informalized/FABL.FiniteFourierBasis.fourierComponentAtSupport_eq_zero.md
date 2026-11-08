<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.fourierComponentAtSupport_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing Fourier component

**Claim.** If every multi-index whose support is exactly $J$ has zero Fourier coefficient for $f$, then the Fourier component of $f$ at support $J$ is the zero function.

**Proof.** Expand the component as the finite sum over multi-indices with support $J$. For each index in this sum, the hypothesis makes its Fourier coefficient zero, so its scalar multiple of the corresponding product function is the zero function. Thus every summand vanishes, and so does the sum.

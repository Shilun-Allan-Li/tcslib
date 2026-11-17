<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.isBent_completeQuadratic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bentness of the complete quadratic function

**Claim.** When $n$ is even, the real sign-valued function defined by the complete quadratic form is bent: every Fourier coefficient has absolute value $(2^{n/2})^{-1}$.

**Proof.** Bentness requires the stated absolute-value identity for every frequency. The complete-quadratic coefficient formula gives exactly this identity at each frequency whenever $n$ is even (`abs_vectorFourierCoeff_completeQuadratic`), so the defining condition for bentness follows.

**Key facts.** `FABL.abs_vectorFourierCoeff_completeQuadratic`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentDual.lean :: FABL.IsSignValued.isBent_bentDual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bentness of the Dual

**Claim.** For even dimension, the dual of a sign-valued function is bent: every Fourier coefficient of the dual has absolute value $2^{-n/2}$.

**Proof.** Fix a frequency $x$. The Fourier coefficient of the dual at $x$ equals $\bigl(2^{n/2}\bigr)^{-1}f(x)$ by the dual Fourier coefficient identity (`vectorFourierCoeff_bentDual`). Taking absolute values gives $\bigl|\bigl(2^{n/2}\bigr)^{-1}\bigr|\,|f(x)|$. The sign-valued hypothesis makes the second factor $1$, and $2^{n/2}$ is positive, so the result is $2^{-n/2}$, as required for bentness.

**Key facts.** `FABL.vectorFourierCoeff_bentDual`.

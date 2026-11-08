<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveMomentSharpness.lean :: FABL.sharpEvenMomentNoise_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square of the sharp even-moment noise

**Claim.** For every positive natural number $r$, the square of the sharp even-moment noise is $1/(2r-1)$.

**Proof.** Positivity of $r$ implies $2r-1>0$. Squaring the defining expression gives $(1/\sqrt{2r-1})^2$. The square of a square root of a nonnegative real is its argument (`Real.sq_sqrt`), so this simplifies to $1/(2r-1)$.

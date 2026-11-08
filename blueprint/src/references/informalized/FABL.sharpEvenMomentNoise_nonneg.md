<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveMomentSharpness.lean :: FABL.sharpEvenMomentNoise_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Nonnegative sharp even-moment noise

**Claim.** For every natural number $r$, the sharp even-moment noise is nonnegative.

**Proof.** By definition, the noise is the reciprocal of the square root of $2r-1$. The square root is nonnegative, and the reciprocal is well-defined and nonnegative when its argument is positive. When $r=0$, the square root is of $-1$ in the real numbers, so the definition's real square root is zero and the reciprocal is not defined as a finite real; however, the supplied proof's positivity step establishes the stated inequality from the Lean definition and its arithmetic simplification.

**Caveat.** The definition gives $1/\sqrt{2r-1}$, which at $r=0$ involves division by zero because the real square root of $-1$ is zero. The proof source's `positivity` result is not explained by the supplied information, so the $r=0$ case cannot be reconciled with the stated definition.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SparsePolynomialApproximation.lean :: FABL.fourierOneNorm_pos_of_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Fourier one-norm

**Claim.** If a real-valued function on the sign cube is not identically zero, then its Fourier one-norm is strictly positive.

**Proof.** Since $f$ is not identically zero, there is a point $x$ with $f(x)\ne0$. Hence $|f(x)|>0$. The pointwise bound of the absolute value of a function by its Fourier one-norm (`abs_apply_le_fourierOneNorm`) gives $|f(x)|\le \|f\|_1$, so the Fourier one-norm is strictly positive.

**Key facts.** `FABL.abs_apply_le_fourierOneNorm`.

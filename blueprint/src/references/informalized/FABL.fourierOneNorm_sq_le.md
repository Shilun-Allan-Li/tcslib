<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/FourierNorms.lean :: FABL.fourierOneNorm_sq_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier norm of a square

**Claim.** The Fourier one-norm of the pointwise square of a real-valued function is at most the square of its Fourier one-norm.

**Proof.** Apply the product inequality for the Fourier one-norm (\texttt{fourierOneNorm_pointwise_mul_le}) to the function paired with itself. Its pointwise product with itself is its pointwise square, and the product of the two norms is the square of the norm. This gives the stated bound.

**Key facts.** `FABL.fourierOneNorm_pointwise_mul_le`.

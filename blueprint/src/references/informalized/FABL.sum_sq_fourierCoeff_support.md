<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HomogeneousMoments.lean :: FABL.sum_sq_fourierCoeff_support -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parseval Identity on Fourier Support

**Claim.** The sum of squared Fourier coefficients over the Fourier support equals the uniform average of the square of the function on the sign cube.

**Proof.** First extend the sum from the Fourier support to all coordinate subsets. Every omitted subset has Fourier coefficient zero by the definition of support, so this extension does not change the sum. Parseval's identity (FABL.parseval) identifies the resulting sum over all subsets with the uniform inner product of the function with itself. In the real-valued setting this inner product is the uniform average of $f(x)^2$, as claimed.

**Key facts.** `FABL.parseval`.

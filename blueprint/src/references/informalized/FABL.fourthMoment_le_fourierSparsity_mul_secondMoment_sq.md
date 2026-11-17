<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HomogeneousMoments.lean :: FABL.fourthMoment_le_fourierSparsity_mul_secondMoment_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth moment and Fourier sparsity

**Claim.** The fourth moment of $f$ is at most its Fourier sparsity times the square of its second moment.

**Proof.** First write $f(x)^4=f(x)^2f(x)^2$ and take expectations. The pointwise estimate that $f(x)^2$ is at most the Fourier sparsity times $\mathbb E_y[f(y)^2$ (the squared-value bound from Fourier sparsity, `sq_le_fourierSparsity_mul_secondMoment`) can be multiplied by the nonnegative factor $f(x)^2$. Taking expectations then bounds the fourth moment by the expectation of $s(\mathbb E_y f(y)^2)f(x)^2$, where $s$ is the Fourier sparsity. Pull the constant and the inner expectation outside the outer expectation; the result is $s(\mathbb E_x f(x)^2)^2$.

**Key facts.** `FABL.sq_le_fourierSparsity_mul_secondMoment`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.uniformLpNorm_six_pow_eq_expect_six -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sixth moment identity

**Claim.** For a finite set $\Omega$ and $f:\Omega\to\mathbb R$, the sixth power of the uniform $L^6$ norm of $f$ equals the uniform mean of $f(x)^6$.

**Proof.** Unfold the norm. At points where $f(x)=0$, the sixth absolute moment and $f(x)^6$ agree. Otherwise, express the sixth real power of $|f(x)|$ as a product of three second powers, using $6=2+2+2$. Since $|f(x)|^2=f(x)^2$, this product is $f(x)^6$. Averaging the pointwise identity identifies the two moments. The latter mean is nonnegative because it averages sixth powers. Applying the integer-power rule for a nonnegative base then cancels the outer exponent $1/6$ and gives the stated equality.

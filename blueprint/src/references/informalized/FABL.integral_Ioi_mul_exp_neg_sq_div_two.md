<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.integral_Ioi_mul_exp_neg_sq_div_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Gaussian Exponential Integral

**Claim.** The integral of $x\exp(-x^2/2)$ over $x>0$ equals $1$.

**Proof.** Regard the real integral as a complex integral by applying the real-to-complex integral identity. The complex Gaussian integral formula gives $\int_0^\infty x\exp(-b x^2)\,dx=1/(2b)$ for positive real part of $b$; take $b=1/2$ to obtain $1$. The real and complex integrands agree because the complex exponent is the complexification of the real exponent, and the resulting complex equality yields the asserted real one.

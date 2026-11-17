<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.integral_posPart_standardGaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Part Mean of a Standard Gaussian

**Claim.** For a standard Gaussian random variable $X$, the expectation of $X^+=\max(X,0)$ is $1/\sqrt{2\pi}$.

**Proof.** Express integration against the standard Gaussian as integration against its density. Since $x^+$ vanishes for $x\le0$ and equals $x$ for $x>0$, the density integral reduces to the positive half-line integral of the density times $x$. Factor out the density's constant $(2\pi)^{-1/2}$. The remaining integral is $\int_0^\infty x e^{-x^2/2}\,dx=1$ (\(\texttt{integral\_Ioi\_mul\_exp\_neg\_sq\_div\_two}\)), yielding $(2\pi)^{-1/2}=1/\sqrt{2\pi}$.

**Key facts.** `FABL.integral_Ioi_mul_exp_neg_sq_div_two`.

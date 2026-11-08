<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.uniformLpNorm_fourThird_sq_of_zeroOne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth-Third Norm of an Indicator

**Claim.** If $f$ takes only the values $0$ and $1$ on the Boolean cube and has uniform mean $\alpha$, then the square of its uniform $L^{4/3}$ norm is $\alpha^{3/2}$.

**Proof.** First, $\alpha\ge 0$: it is the average of values that are either $0$ or $1$. The same two-valued property gives $|f(x)|^{4/3}=f(x)$ at every point, so the moment inside the definition of the uniform norm is exactly the mean $\alpha$. Thus the norm is $\alpha^{(3/4)}$, since the reciprocal of $4/3$ is $3/4$. Squaring yields $\alpha^{3/2}$; the nonnegativity of $\alpha$ justifies the real-power exponent rules used here.

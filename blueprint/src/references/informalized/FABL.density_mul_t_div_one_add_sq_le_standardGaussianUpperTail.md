<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianMillsRatio.lean :: FABL.density_mul_t_div_one_add_sq_le_standardGaussianUpperTail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Lower Tail Bound

**Claim.** For $t>0$, $\frac{t}{1+t^2}$ times the standard Gaussian density at $t$ is at most the standard Gaussian upper tail beyond $t$.

**Proof.** Set $p(x)=\phi(x)+\phi(x)/x^2$, where $\phi$ is the standard Gaussian density. The integral identity for this function gives $\int_t^\infty p(x)\,dx=\phi(t)/t$ (\texttt{integral\_standardGaussianDensity\_add\_div\_sq}). On $x>t>0$, we have $1/x^2\le1/t^2$, so $p(x)\le(1+1/t^2)\phi(x)$. Integrating this comparison and using the identity that the Gaussian upper tail is the integral of its density (\texttt{standardGaussianUpperTail\_eq\_integral\_density}) yields $\phi(t)/t\le(1+1/t^2)P\{g>t\}$. Multiplying by the positive factor $t^2/(1+1/t^2)$ and simplifying gives the stated inequality.

**Key facts.** `FABL.integral_standardGaussianDensity_add_div_sq`, `FABL.standardGaussianUpperTail_eq_integral_density`.

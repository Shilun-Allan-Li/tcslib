<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/PolynomialApproximation.lean :: BooleanAnalysis.GaussianSpace.gaussianTorusFourier_mem_polynomial_closure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian torus Fourier approximation

**Claim.** For finite $p\ge1$, the Gaussian torus Fourier character with frequency $m$ belongs to the $L^p$ closure of restrictions of complex polynomials.

**Proof.** Write the character pulled back to Gaussian space as an exponential of a real linear functional. Specifically, for each coordinate set $a_i=2\pi(m(i,\mathrm{false})+\sqrt2\,m(i,\mathrm{true}))$, and take the complex linear functional $L(x)=i\sum_i a_i x_i$. The exponential approximation result says that any such function $x\mapsto\exp(L(x))$, as an element of Gaussian $L^p$, lies in the closure of the polynomial restrictions. The Fourier character agrees almost everywhere with this exponential: its representative is the character evaluated at the torus image, and the explicit formula for that value is $\exp(i\sum_i a_i x_i)$. Therefore the Fourier character has the same membership in the polynomial closure.

**Key facts.** `BooleanAnalysis.GaussianSpace.exp_linear_mem_gaussianPolynomial_closure`, `BooleanAnalysis.GaussianSpace.coeFn_gaussianTorusFourierLp`, `BooleanAnalysis.GaussianSpace.mFourier_gaussianTorusMap`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Replacement.lean :: BooleanAnalysis.GaussianSpace.independent_affine_integral -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integral formula for an independent affine input

**Claim.** When $W$ is independent of $(A,D)$, the expectation of $\psi(A+DW)$ equals the integral, under the law of $(A,D)$, of the function $q(a,d)=\mathbb E[\psi(a+dW)]$; this function is integrable under that law.

**Proof.** Define $F((a,d),w)=\psi(a+dw)$. This is continuous, hence measurable. Independence says that the joint law of $((A,D),W)$ is the product of the law of $(A,D)$ and the law of $W$. The assumed integrability of $F((A,D),W)$ therefore transfers to integrability of $F$ under that product law, using the change-of-variables formula for the joint law. Fubini's theorem now gives integrability of the section integral $q(a,d)=\int F((a,d),w)\,d\mathcal L(W)(w)$ under the law of $(A,D)$, and identifies the product integral with the integral of $q$. Finally, changing variables from the original probability space to the joint law identifies that product integral with $\mathbb E[\psi(A+DW)]$, proving the formula.

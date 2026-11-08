<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.hasDerivAt_gaussianPDFReal_posVariance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of a Gaussian density

**Claim.** For mean $\mu$, variance $v>0$, and point $x$, the Gaussian density is differentiable at $x$, with derivative $-\frac{x-\mu}{v}$ times its value at $x$.

**Proof.** Write the density as its constant normalizing factor times $\exp\!\left(-\frac{(y-\mu)^2}{2v}\right)$. By the power rule and constant-factor rules, the exponent has derivative $-(x-\mu)/v$ at $x$. The chain rule for the exponential then gives the derivative of the exponential as this exponent derivative times the exponential itself. Multiplication by the constant normalizing factor yields $-\frac{x-\mu}{v}$ times the Gaussian density at $x$, as required.

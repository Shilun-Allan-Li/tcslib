<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/SubGaussian.lean :: integral_exp_mul_sq_le_of_subgaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential square moment bound

**Claim.** If every exponential tilt of a measurable random variable $Z$ is integrable and its moment-generating function is bounded by the sub-Gaussian estimate with parameter $\sigma^2$, then for $t\ge0$ with $2\sigma^2t<1$, the function $e^{tZ^2}$ is integrable and its expectation is at most $(1-2\sigma^2t)^{-1/2}$.

**Proof.** For each value $z$, the Gaussian integral identity expresses $e^{tz^2}$ as the average of $e^{\sqrt{2t}\,zg}$ when $g$ has the standard Gaussian distribution (`exp_mul_sq_eq_integral_gaussian`). The integrand on the product of the original probability space and the Gaussian space is measurable, so Tonelli's theorem lets us swap the two nonnegative integrals. For fixed $g$, the inner expectation is the moment-generating function of $Z$ at $\sqrt{2t}\,g$. The assumed sub-Gaussian bound therefore bounds it by $e^{\sigma^2t g^2}$, using $t\ge0$ to square the square root. Integrating this bound in $g$ gives $(1-2\sigma^2t)^{-1/2}$ by the Gaussian exponential-square integral formula (`integral_exp_mul_sq_gaussianReal_zero`), whose integrability condition is exactly $2\sigma^2t<1$. Thus the nonnegative integral of $e^{tZ^2}$ is finite and has the claimed bound. Measurability of $Z$ gives strong measurability of the integrand, and finiteness of its nonnegative integral gives its integrability; converting the integral bound back from the nonnegative reals yields the stated expectation inequality.

**Key facts.** `exp_mul_sq_eq_integral_gaussian`.

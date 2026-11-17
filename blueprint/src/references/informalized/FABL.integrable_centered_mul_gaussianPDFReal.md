<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.integrable_centered_mul_gaussianPDFReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of a Centered Gaussian Density

**Claim.** For $\mu\in\mathbb{R}$ and nonzero $v\ge0$, the function $x\mapsto(x-\mu)g_{\mu,v}(x)$ is integrable on $\mathbb{R}$.

**Proof.** Under the Gaussian measure with mean $\mu$ and parameter $v$, the identity function has a finite first moment; consequently its centered version $x\mapsto x-\mu$ is integrable. Since $v\ne0$, this Gaussian measure is given by its density with respect to Lebesgue measure. The integral of the absolute value of a function against a measure with density is the integral of its absolute value times that density against Lebesgue measure. Applying this density conversion to the centered function gives integrability of $x\mapsto(x-\mu)g_{\mu,v}(x)$.

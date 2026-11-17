<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/IndicatorSmoothing.lean :: BooleanAnalysis.GaussianSpace.integral_averagedGaussianIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Mean Preservation

**Claim.** For measurable $A\subseteq\mathbb R^n$ and any angle $\theta$, the Gaussian integral of the averaged indicator $u_\theta$ equals $\gamma_n(A)$.

**Proof.** Let $\mu=\gamma_n$ and let $E$ be the set of pairs $(x,y)$ for which $\cos\theta\,x+\sin\theta\,y\in A$. For each fixed $x$, the averaged indicator is the measure of the section $E_x$ (`averagedGaussianIndicator_eq_real_measure`). Tonelli's theorem for this measurable set therefore identifies its integral over $x$ with the product measure $(\mu\times\mu)(E)$. The map $(x,y)\mapsto(\cos\theta\,x+\sin\theta\,y,-\sin\theta\,x+\cos\theta\,y)$ preserves the product Gaussian measure (`measurePreserving_gaussianRotation`). Under this rotation, $E$ is the preimage of $A$ under projection onto the first coordinate. That coordinate has law $\mu$, since projection preserves the product measure. Hence $(\mu\times\mu)(E)=\mu(A)$, as required.

**Key facts.** `BooleanAnalysis.GaussianSpace.averagedGaussianIndicator_eq_real_measure`, `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianRotation`.

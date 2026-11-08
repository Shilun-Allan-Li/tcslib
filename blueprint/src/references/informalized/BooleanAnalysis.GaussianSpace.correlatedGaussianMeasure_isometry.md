<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise.lean :: BooleanAnalysis.GaussianSpace.correlatedGaussianMeasure_isometry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Isometric Invariance of Correlated Gaussian Measure

**Claim.** For $\rho\in[-1,1]$, applying the same linear isometry $Q$ to both vectors leaves the correlated Gaussian measure unchanged.

**Proof.** Write $C(g,g')=(g,\rho g+\sqrt{1-\rho^2}g')$ for the map defining the correlated measure, and let $P(g,g')=(Qg,Qg')$. The Gaussian product measure is preserved by $P$, since each copy of the standard Gaussian product measure is invariant under the isometry ($\texttt{measurePreserving\_gaussianIsometry}$). Moreover, $C$ and $P$ commute: linearity of $Q$ gives $Q(\rho g+\sqrt{1-\rho^2}g')=\rho Qg+\sqrt{1-\rho^2}Qg'$. Thus pushing the product Gaussian measure forward by $C$ and then by $P$ gives the same result as pushing it forward by $P$ and then by $C$. The latter equals its pushforward by $C$, because $P$ preserves the product measure. This proves the asserted invariance.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianIsometry`.

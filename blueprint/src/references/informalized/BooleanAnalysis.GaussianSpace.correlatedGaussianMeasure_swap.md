<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise.lean :: BooleanAnalysis.GaussianSpace.correlatedGaussianMeasure_swap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exchange Symmetry of Correlated Gaussian Measure

**Claim.** For $\rho\in[-1,1]$, exchanging the two vectors leaves the correlated Gaussian measure unchanged.

**Proof.** Write $C(g,g')=(g,\rho g+\sqrt{1-\rho^2}g')$. Introduce the rotation-reflection map $R(g,g')=(\rho g+\sqrt{1-\rho^2}g',\sqrt{1-\rho^2}g-\rho g')$. The map $R$ preserves the product Gaussian measure: it is the Gaussian-preserving rotation-reflection with cosine $\rho$ and sine $\sqrt{1-\rho^2}$ ($\texttt{measurePreserving\_gaussianReflection}$). A direct calculation using $\rho^2+(1-\rho^2)=1$ shows that $C\circ R$ equals the swap map composed with $C$. Consequently, swapping the coordinates after pushing forward by $C$ has the same effect as first applying $R$ and then pushing forward by $C$. Since $R$ preserves the product Gaussian measure, the resulting pushforward is unchanged, proving the symmetry.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianReflection`.

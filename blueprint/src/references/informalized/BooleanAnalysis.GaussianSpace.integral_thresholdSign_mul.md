<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Halfspace.lean :: BooleanAnalysis.GaussianSpace.integral_thresholdSign_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product of Threshold Signs

**Claim.** If $X$ and $Y$ each have the standard Gaussian distribution on a probability space, then the integral of the product of their threshold signs is $4\mu(X\le0,\,Y\le0)-1$.

**Proof.** Let $A=\{X\le0\}$ and $B=\{Y\le0\}$. Each event is measurable, and each has probability $1/2$: the distribution assumptions identify their probabilities with the standard Gaussian probability of $(-\infty,0]$, which is $1/2$ (`standardGaussianCDF_zero`). The Gaussian law has no atoms, so $X$ and $Y$ are nonzero almost everywhere. Away from their zero sets, a direct check of the four sign possibilities gives the almost-everywhere identity $\sigma(X)\sigma(Y)=4\mathbf 1_{A\cap B}-2\mathbf 1_A-2\mathbf 1_B+1$. Integrating this identity is valid because these indicators and the constant are integrable. Their integrals are respectively the probabilities of $A\cap B$, $A$, and $B$, and the constant integrates to one. Substituting $\mu(A)=\mu(B)=1/2$ gives $4\mu(A\cap B)-1$, as claimed.

**Key facts.** `BooleanAnalysis.GaussianSpace.standardGaussianCDF_zero`.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProfileApproximation.lean :: BooleanAnalysis.GaussianSpace.closedGaussianProfile_endpoint_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian profile endpoint bound

**Claim.** For every $\varepsilon>0$, there is $C>0$ such that for every $p\in[0,1]$ and $b\in\{0,1\}$, the closed Gaussian profile satisfies $U(p)\le\varepsilon+C|p-b|$.

**Proof.** Continuity of the closed Gaussian profile on the compact interval $[0,1]$ gives a uniform bound $M$ there, and uniform continuity gives a distance $\delta>0$ such that points within $\delta$ have profile values differing by less than $\varepsilon$. Set $C=\max(M,1)/\delta>0$. For either endpoint $b=0$ or $b=1$, the profile vanishes at $b$. If $|p-b|<\delta$, uniform continuity and nonnegativity of the profile show $U(p)\le\varepsilon$. Otherwise, $\delta\le|p-b|$, and the bound $U(p)\le M\le\max(M,1)\le C|p-b|$ gives the result. The proof uses nonnegativity of the closed profile (`BooleanAnalysis.GaussianSpace.closedGaussianProfile_nonneg`) and its continuity on the interval (`BooleanAnalysis.GaussianSpace.continuousOn_closedGaussianProfile`).

**Key facts.** `BooleanAnalysis.GaussianSpace.continuousOn_closedGaussianProfile`, `BooleanAnalysis.GaussianSpace.closedGaussianProfile_nonneg`.

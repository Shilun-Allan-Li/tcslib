<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.strictMono_standardGaussianCDF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict increase of the Gaussian CDF

**Claim.** The standard Gaussian distribution function $\Phi$ is strictly increasing on $\mathbb R$.

**Proof.** Take $x<y$. The distribution function at $y$ is the measure of $(-\infty,y]$, while at $x$ it is the measure of $(-\infty,x]$. Decomposing the former into $(-\infty,x]$ and $(x,y]$ shows that their difference is the Gaussian measure of $(x,y]$. The Gaussian assigns positive measure to the open interval $(x,y)$, and hence also to $(x,y]$. Thus $\Phi(x)<\Phi(y)$.

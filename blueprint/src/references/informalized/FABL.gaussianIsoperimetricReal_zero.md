<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.gaussianIsoperimetricReal_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Isoperimetric Value at Zero

**Claim.** Let $q:(0,1)\to\mathbb{R}$ be the inverse of the standard Gaussian upper-tail function, and let $I:\mathbb{R}\to\mathbb{R}$ extend $\alpha\mapsto\varphi(q(\alpha))$ from $(0,1)$, where $\varphi$ is the standard Gaussian density. Then $I(0)=0$.

**Proof.** The value of the extension at the left endpoint is the limit of its interior profile as the argument approaches $0$ from above. That interior profile tends to $0$ at the endpoint (\texttt{FABL.tendsto\_gaussianIsoperimetricInterior\_zero}), hence the extended value at $0$ is $0$.

**Key facts.** `FABL.tendsto_gaussianIsoperimetricInterior_zero`.

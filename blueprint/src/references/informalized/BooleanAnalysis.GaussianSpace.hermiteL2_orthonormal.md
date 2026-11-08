<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basis.lean :: BooleanAnalysis.GaussianSpace.hermiteL2_orthonormal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orthonormality of Hermite functions

**Claim.** For every dimension $n$, the multivariate normalized Hermite functions form an orthonormal family in $L^2(\mathbb R^n,\gamma_n)$, where $\gamma_n$ is the product of $n$ standard Gaussian probability measures.

**Proof.** For any two multi-indices $\alpha$ and $\beta$, the inner product of their $L^2$ Hermite classes is $1$ if $\alpha=\beta$ and $0$ otherwise (`inner_hermiteL2`). This is exactly the inner-product characterization of an orthonormal family, so the family is orthonormal.

**Key facts.** `BooleanAnalysis.GaussianSpace.inner_hermiteL2`.

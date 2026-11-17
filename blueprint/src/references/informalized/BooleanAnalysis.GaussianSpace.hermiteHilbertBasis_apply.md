<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basis.lean :: BooleanAnalysis.GaussianSpace.hermiteHilbertBasis_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hermite basis vectors

**Claim.** For every natural number $n$ and multi-index $\alpha:\{1,\ldots,n\}\to\mathbb N$, the Hilbert basis vector indexed by $\alpha$ is the $L^2$ equivalence class of the Hermite function indexed by $\alpha$, with respect to the product of $n$ standard Gaussian measures.

**Proof.** By definition, the Hermite Hilbert basis is built from the family of $L^2$ classes of Hermite functions. Evaluating that basis at $\alpha$ gives precisely the family member indexed by $\alpha$, which is the stated $L^2$ class.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basis.lean :: BooleanAnalysis.GaussianSpace.exists_memLp_hermiteCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Realizing square-summable Hermite coefficients

**Claim.** Every square-summable real family indexed by multi-indices is the Hermite coefficient family of some function in $L^2$ for product standard Gaussian measure.

**Proof.** The summability of $\sum_\alpha c_\alpha^2$ says exactly that the coefficient family $c$ belongs to the Hilbert space $\ell^2$ indexed by the multi-indices. Apply the inverse of the Hermite Hilbert basis coordinate map to this family, obtaining an element $v$ of the Gaussian $L^2$ space. Choose a function representative $g$ of $v$; by construction it belongs to $L^2$. The Hermite basis representation theorem identifies the $\alpha$-coordinate of the class of any such $g$ with its Hermite coefficient at $\alpha$ (\texttt{hermiteHilbertBasis_repr_toLp}). Since the coordinates of $v$ are $c_\alpha$, every coefficient of $g$ is the prescribed one.

**Key facts.** `BooleanAnalysis.GaussianSpace.hermiteHilbertBasis_repr_toLp`.

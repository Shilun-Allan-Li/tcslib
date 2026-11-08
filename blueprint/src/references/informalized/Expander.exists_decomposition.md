<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Walks.lean :: Expander.exists_decomposition -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Contractive Matrix Decomposition

**Claim.** A symmetric stochastic matrix whose action on vectors orthogonal to the constant vector has norm bounded by $\lambda$ can be written as $(1-\lambda)J+\lambda C$, where $J$ is the uniform matrix and $C$ has Euclidean operator norm at most $1$.

**Proof.** First consider $\lambda=0$. The bound on the action of the matrix on every vector orthogonal to the uniform vector forces that action to vanish. The uniform vector itself is fixed by a symmetric stochastic matrix (Expander.mulVec_uniform). For each coordinate vector, subtract its uniform component; the difference is orthogonal to the uniform vector, so the matrix sends that difference to zero and sends the uniform component to itself. Hence every coordinate vector is sent to the uniform vector. Reading off coordinates shows that the matrix is exactly $J$, giving the claimed decomposition with $C=0$.

Now suppose $\lambda>0$ and set $C=\lambda^{-1}(A-(1-\lambda)J)$. Rearrangement gives the required decomposition. To prove contraction, decompose an arbitrary vector $v$ as $p+w$, where $p$ is its component along the uniform vector and $w$ is orthogonal to it. The uniform matrix fixes $p$ and annihilates $w$, while $A$ fixes $p$. Thus $Cv=p+\lambda^{-1}Aw$. Symmetry makes the two components $p$ and $\lambda^{-1}Aw$ orthogonal: the identity transferring $A$ across the inner product (Expander.inner_toCLM_right), together with the fact that $A$ fixes the uniform vector, gives this orthogonality. The spectral bound on the orthogonal component (Expander.norm_mulVec_le_lambda) yields $\|\lambda^{-1}Aw\|\leq\|w\|$. By Pythagoras, $\|Cv\|^2\leq\|p\|^2+\|w\|^2=\|v\|^2$, so $C$ has operator norm at most $1$. The zero-dimensional case is immediate because its vector space is trivial.

**Key facts.** `Expander.mulVec_uniform`, `Expander.norm_mulVec_le_lambda`, `Expander.inner_toCLM_right`.

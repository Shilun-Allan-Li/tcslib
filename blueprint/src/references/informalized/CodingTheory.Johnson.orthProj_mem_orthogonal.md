<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: CodingTheory.Johnson.orthProj_mem_orthogonal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Projection off a unit vector lands in the orthogonal complement

**Claim.** Let $V$ be a real inner product space and let $u, v \in V$ with $\|u\| = 1$. Then the vector $v - \langle u, v\rangle\, u$ lies in the orthogonal complement $(\mathrm{span}_{\mathbb{R}}\{u\})^{\perp}$ of the line spanned by $u$. Equivalently, subtracting from $v$ its component along the unit vector $u$ leaves a vector orthogonal to every multiple of $u$.

**Proof.** By definition, a vector $w$ belongs to $(\mathrm{span}_{\mathbb{R}}\{u\})^{\perp}$ precisely when $\langle x, w\rangle = 0$ for every $x$ in $\mathrm{span}_{\mathbb{R}}\{u\}$. So fix an arbitrary element $x$ of that line; we must show $\langle x, v - \langle u,v\rangle\, u\rangle = 0$.

1. **Reduce to a scalar multiple of $u$.** Since $x$ lies in the span of the single vector $u$, it is a real multiple of it: $x = k\,u$ for some $k \in \mathbb{R}$ (this is the characterization of the span of a singleton). It therefore suffices to prove
\[
\bigl\langle k\,u,\; v - \langle u,v\rangle\, u\bigr\rangle = 0.
\]

2. **Expand by bilinearity.** Pulling the scalar $k$ out of the left argument, distributing over the difference in the right argument, and pulling the scalar $\langle u,v\rangle$ out of the right argument, we get
\[
\bigl\langle k\,u,\; v - \langle u,v\rangle\, u\bigr\rangle
= k\Bigl(\langle u, v\rangle - \langle u,v\rangle\,\langle u, u\rangle\Bigr).
\]
All three expansions are the elementary linearity rules of a real inner product.

3. **Use that $u$ is a unit vector.** For a real inner product, $\langle u, u\rangle = \|u\|^{2}$, and the hypothesis $\|u\| = 1$ gives $\langle u, u\rangle = 1$. Substituting,
\[
k\Bigl(\langle u, v\rangle - \langle u,v\rangle\cdot 1\Bigr) = k\cdot 0 = 0.
\]

Since the inner product of $x$ with $v - \langle u,v\rangle\, u$ vanishes for an arbitrary $x$ on the line, the vector $v - \langle u,v\rangle\, u$ is orthogonal to that line, i.e. it lies in $(\mathrm{span}_{\mathbb{R}}\{u\})^{\perp}$. $\qquad\blacksquare$

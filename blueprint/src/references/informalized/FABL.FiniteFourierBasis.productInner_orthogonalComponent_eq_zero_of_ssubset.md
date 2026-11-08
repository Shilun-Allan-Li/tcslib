<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.FiniteFourierBasis.productInner_orthogonalComponent_eq_zero_of_ssubset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orthogonality for a strict subset

**Claim.** If $T\subsetneq S$ and $g$ depends only on coordinates in $T$, then the inner product of the orthogonal component of $f$ on $S$ with $g$ is zero.

**Proof.** Since $T\subsetneq S$, we have $S\not\subseteq T$: otherwise the two inclusions would force $S=T$. Apply the result that an orthogonal component indexed by a set not contained in the coordinate set on which the other function depends has zero inner product (\texttt{productInner_orthogonalComponent_eq_zero_of_not_subset}).

**Key facts.** `FABL.FiniteFourierBasis.productInner_orthogonalComponent_eq_zero_of_not_subset`.

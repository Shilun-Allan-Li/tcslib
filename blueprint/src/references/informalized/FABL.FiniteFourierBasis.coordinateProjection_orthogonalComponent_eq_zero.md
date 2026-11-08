<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.FiniteFourierBasis.coordinateProjection_orthogonalComponent_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Projection of an orthogonal component

**Claim.** If coordinate $i$ belongs to the support set $S$, then projecting the orthogonal component supported on $S$ onto all coordinates except $i$ gives zero.

**Proof.** The coordinate projection at $i$ is projection onto $T=\mathrm{Fin}\,n\setminus\{i\}$. The projection formula for an orthogonal component says that projecting the component supported on $S$ onto coordinates in $T$ returns that component if $S\subseteq T$, and returns zero otherwise (\texttt{projectOnCoordinates_orthogonalComponent}). Since $i\in S$, the inclusion $S\subseteq T$ is impossible: it would imply $i\in T$, although $T$ excludes $i$. Hence the projection is zero.

**Key facts.** `FABL.FiniteFourierBasis.projectOnCoordinates_orthogonalComponent`.

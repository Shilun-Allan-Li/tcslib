<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.FiniteFourierBasis.orthogonalComponent_dependsOnly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate dependence of components

**Claim.** The orthogonal component of a function at a coordinate set $S$ depends only on the coordinates in $S$.

**Proof.** By definition, the orthogonal component at $S$ is the Fourier component at support $S$. The Fourier component depends only on the coordinates in its specified support ($\texttt{FABL.FiniteFourierBasis.fourierComponentAtSupport_dependsOnly}$), which gives the claim.

**Key facts.** `FABL.FiniteFourierBasis.fourierComponentAtSupport_dependsOnly`.

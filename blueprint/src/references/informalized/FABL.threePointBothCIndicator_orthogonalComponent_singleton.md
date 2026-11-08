<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.threePointBothCIndicator_orthogonalComponent_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton Fourier Component

**Claim.** For each coordinate $i\in\{0,1\}$, the singleton-support component of the indicator that both coordinates equal $c$ is $2/9$ when $x_i=c$ and $-1/9$ otherwise.

**Proof.** Evaluate at an arbitrary pair $x$. The Möbius formula (\texttt{FiniteFourierBasis.orthogonalComponent\_eq\_mobius}) writes the component as the alternating sum of the projections indexed by subsets of $\{i\}$, namely $\varnothing$ and $\{i\}$. Their projection values are given by \texttt{projectOnCoordinates\_threePointBothCIndicator}: the coordinate in the chosen subset contributes its indicator of $c$, while the other contributes $1/3$. Thus the component is the projection for $\{i\}$ minus the projection for $\varnothing$. If $x_i=c$, this difference is $1/3-1/9=2/9$; otherwise it is $0-1/9=-1/9$. The proof checks the two possible coordinates, which gives the assertion for every $i$.

**Key facts.** `FABL.FiniteFourierBasis.orthogonalComponent_eq_mobius`, `FABL.powerset_singleton_eq`, `FABL.projectOnCoordinates_threePointBothCIndicator`.

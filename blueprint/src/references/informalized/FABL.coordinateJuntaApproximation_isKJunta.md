<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.coordinateJuntaApproximation_isKJunta -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Approximation Is a Junta

**Claim.** The coordinate junta approximation based on $J$ is a $J.card$-junta.

**Proof.** Choose $J$ itself as the set of coordinates witnessing the junta property; its size is exactly $J.card$. If two inputs agree on $J$, the coordinate projection of the function has the same value on them, because that projection depends only on coordinates in $J$ (the dependence property of coordinate projection, `FABL.projectOnCoordinates_dependsOnly`). Applying the same threshold-sign map to these equal values preserves equality. Hence the coordinate junta approximation also depends only on $J$, as required.

**Key facts.** `FABL.projectOnCoordinates_dependsOnly`.

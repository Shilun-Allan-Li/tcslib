<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdInfluence.lean :: FABL.coordinateSign_isCoordinateIndependent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independence of a Sign Coordinate

**Claim.** If $i$ and $j$ are distinct coordinates, then the sign at coordinate $j$ is unchanged when coordinate $i$ is replaced by any sign.

**Proof.** Fix a sign vector $x$ and a sign $b$. Since $j\ne i$, updating coordinate $i$ leaves coordinate $j$ unchanged (`setCoordinate_apply_of_ne`). Applying the real-valued sign map to these equal coordinates gives the desired equality.

**Key facts.** `FABL.setCoordinate_apply_of_ne`.

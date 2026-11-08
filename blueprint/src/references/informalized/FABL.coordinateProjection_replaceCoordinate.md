<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.coordinateProjection_replaceCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Projection is invariant under replacing the projected coordinate

**Claim.** The projection onto all coordinates except $i$ has the same value at an input and at that input with coordinate $i$ replaced.

**Proof.** The projection onto a coordinate set depends only on the input's coordinates in that set (\texttt{FABL.projectOnCoordinates\_dependsOnly}). For the set of all coordinates except $i$, replacing coordinate $i$ leaves every coordinate in the set unchanged. The two projected values are therefore equal.

**Key facts.** `FABL.projectOnCoordinates_dependsOnly`.

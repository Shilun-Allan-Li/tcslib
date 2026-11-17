<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/BooleanInfluence.lean :: FABL.setCoordinate_setCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two Successive Coordinate Updates

**Claim.** Updating one coordinate first by $a$ and then by $b$ has the same effect as updating it directly by $b$.

**Proof.** Both sides agree at every coordinate. At the chosen coordinate, each has value $b$; at every other coordinate, both retain the original value of the vector. Thus the two updated vectors are equal.

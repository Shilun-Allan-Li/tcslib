<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdUniformStability.lean :: FABL.identifiedFrequency_card_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Identified frequency cardinality bound

**Claim.** For a map from the source coordinates to target coordinates, the number of target coordinates receiving an odd number of elements of $S$ is at most $|S|$.

**Proof.** Every target coordinate counted in the identified set receives an odd, hence positive, number of elements of $S$. It therefore has at least one preimage in $S$, so it lies in the image of $S$. The identified set is thus contained in that image. Taking cardinalities bounds its size by the image size, which is at most $|S|`.

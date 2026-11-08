<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.juntaRestrictionDimension_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dimension of the Free Coordinates

**Claim.** For any finite set of coordinates P among the n coordinates, the number of coordinates outside P is at most n.

**Proof.** The free coordinates form a subtype of `Fin n`, namely the coordinates that do not belong to P. A subtype of a finite set has cardinality at most that of the ambient set. Since `Fin n` has cardinality n, the free-coordinate count is at most n.

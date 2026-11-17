<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.length_f₂LinearCoordinateList -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear Coordinate List Length

**Claim.** For every finite, encodable type of coordinates, the linear coordinate list has length equal to the number of elements of that type.

**Proof.** The linear coordinate list is the sorted enumeration of the finite type. Sorting its universal enumeration changes only the order, not the number of entries. Its length is therefore the cardinality of the type.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.fixedCoordinateProjectionLinear_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Projection Formula

**Claim.** For any position outside $J$, the projected vector’s coordinate is the original vector’s coordinate at the corresponding index.

**Proof.** By definition, the linear map `fixedCoordinateProjectionLinear` sends a vector $x$ to the function whose value at $q$ is $x$ evaluated at the index corresponding to $q$. Thus the two sides are definitionally equal.

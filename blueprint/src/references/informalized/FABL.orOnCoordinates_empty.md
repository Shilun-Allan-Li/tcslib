<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.orOnCoordinates_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# OR on no coordinates

**Claim.** For every $n$, the function that tests whether all coordinates in the empty set equal $1$ is constantly $1$.

**Proof.** Fix an input vector. The condition that every element of the empty set has value $1$ holds vacuously, so the defining conditional returns $1$ at every input. Thus the function is constant with value $1$.

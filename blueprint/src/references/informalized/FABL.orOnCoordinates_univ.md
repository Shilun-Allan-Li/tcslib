<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.orOnCoordinates_univ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# OR on all coordinates

**Claim.** For every $n$, testing whether all coordinates in the full coordinate set equal $1$ gives the OR function.

**Proof.** Fix an input vector. Membership in the full coordinate set imposes no restriction on a coordinate, so requiring every coordinate in that set to equal $1$ is exactly the condition that every coordinate equals $1$. The two defining conditionals therefore agree at every input.

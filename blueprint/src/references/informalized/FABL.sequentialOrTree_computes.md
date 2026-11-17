<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.sequentialOrTree_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness on the Full Coordinate Set

**Claim.** The sequential OR tree on all $n$ coordinates returns $1$ exactly when every coordinate has value $1$, and otherwise returns $-1$.

**Proof.** The sequential OR tree is the auxiliary sequential tree with the full coordinate set available. On that set, the condition that every available coordinate has value $1$ is exactly the defining condition for the OR function (\texttt{orOnCoordinates\_univ}). The auxiliary tree computes the function testing this condition (\texttt{sequentialOrTreeAux\_computes}), so the full sequential OR tree computes the stated function.

**Key facts.** `FABL.orOnCoordinates_univ`, `FABL.sequentialOrTreeAux_computes`.

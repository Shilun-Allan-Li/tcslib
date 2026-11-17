<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordinateDecisionTree.assignCoordinates_apply_of_not_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unqueried Coordinates Remain Unchanged

**Claim.** If coordinate $i$ does not occur in the list $L$, assigning the values of $x$ on the coordinates in $L$ leaves the value of the seed assignment at $i$ unchanged.

**Proof.** Induct on the list, allowing the seed assignment to vary. For the empty list, no updates occur, so the claim is immediate. For a list with head coordinate $j$ and tail $L'$, the hypothesis that $i$ is absent from the list says both that $i\ne j$ and that $i$ is absent from $L'$. The first update changes the seed only at $j$, so its value at $i$ remains the original seed value. Apply the induction hypothesis to the tail with this updated seed; since $i$ is absent from the tail, the remaining assignments also leave its value unchanged.

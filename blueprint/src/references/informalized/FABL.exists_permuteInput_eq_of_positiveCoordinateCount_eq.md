<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/MayTheorem.lean :: FABL.exists_permuteInput_eq_of_positiveCoordinateCount_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Permutation Between Equal-Weight Inputs

**Claim.** If two sign-cube inputs have the same number of positive coordinates, a permutation of coordinates sends the first input to the second.

**Proof.** The sets of positive coordinates of the two inputs have equal cardinality by the hypothesis. A permutation can therefore be chosen that maps the positive-coordinate set of the second input onto that of the first. For each coordinate $i$, this means that the value of the first input at the permuted coordinate is positive exactly when the value of the second input at $i$ is positive. Since each coordinate value is either $1$ or $-1$, this equivalence forces the two values to agree. Hence the permutation sends the first input to the second, coordinate by coordinate.

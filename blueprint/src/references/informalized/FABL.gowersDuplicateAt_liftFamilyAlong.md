<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersDuplicateAt_liftFamilyAlong -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duplication of a Lifted Family

**Claim.** Duplicating the lifted family at the coordinate corresponding to the last input coordinate, with value $b$, is the lift along the restricted embedding of the family obtained by appending $b$ to each input.

**Proof.** Evaluate both families at an arbitrary cube point and an arbitrary spatial point. Their values are obtained by applying the same function to two input cubes, so it suffices to show those cubes agree coordinate by coordinate. Split an input coordinate into the last coordinate and a coordinate among the first $r$. At the last coordinate, inserting $b$ makes the value $b$, just as appending $b$ does. At any earlier coordinate $j$, injectivity of $e$ ensures that $e(j)$ differs from $e$ of the last coordinate; hence updating the lifted cube at the latter coordinate leaves its value at $e(j)$ unchanged. Both constructions therefore give the original cube value at $e(j)$. The input cubes, and thus the two families, agree.

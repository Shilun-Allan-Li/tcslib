<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.juntaRestriction_eq_const_of_dependsOn_of_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction constant on fixed relevant coordinates

**Claim.** If the function depends only on coordinates in $J$ and $J\subseteq P$, then fixing $P$ makes the restriction constant, with value obtained by setting all free coordinates to $1$.

**Proof.** Take any two assignments to the free coordinates, and combine each with the fixed assignment. On every coordinate in $J$, the two combined points agree: since $J\subseteq P$, that coordinate is fixed by the same assignment $z$. The dependence hypothesis therefore forces the function to take the same value on these two points. In particular, its value at any free assignment equals its value when all free coordinates are set to $1$, which is precisely the asserted constancy.

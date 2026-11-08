<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.juntaRestriction_eq_const_of_reindexed_eq_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constancy after reindexing

**Claim.** If the reindexed restriction is constantly equal to $c$, then the restriction itself is constantly equal to $c$.

**Proof.** Fix any assignment $y$ to the free coordinates. Reindex it as a point of the finite-dimensional sign cube using the inverse of the sign-cube equivalence. Evaluating the assumed constant reindexed restriction at that point gives the original restriction evaluated at $y$, because the equivalence followed by its inverse recovers $y$. Thus the restriction has value $c$ at every $y$.

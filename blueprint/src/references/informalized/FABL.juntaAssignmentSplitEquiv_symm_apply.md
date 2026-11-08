<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.juntaAssignmentSplitEquiv_symm_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recombining Split Assignments

**Claim.** Splitting assignments into their fixed and free parts and recombining them recovers the function on all indices whose values are the assigned signs.

**Proof.** Fix an index $i$. If $i\in P$, the inverse of the split equivalence reads the fixed assignment at $i$, so its value is $z_i$. If $i\notin P$, it reads the free assignment at the corresponding free index, so its value is $y_i$. These are exactly the two cases in the definition of the recombined assignment. Since the functions agree at every index, they are equal.

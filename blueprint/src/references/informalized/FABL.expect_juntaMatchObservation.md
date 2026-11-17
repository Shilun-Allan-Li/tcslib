<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.expect_juntaMatchObservation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of Matching a Fixed Assignment

**Claim.** For a fixed set $P$ of coordinates and a fixed sign assignment on $P$, a uniformly random sign vector matches that assignment with probability $2^{-|P|}$.

**Proof.** Split a sign vector into its coordinates on $P$ and its coordinates outside $P$. This is a bijection between the full cube and the product of the fixed-coordinate and free-coordinate assignment spaces, so uniform expectation can be computed by averaging over that product. For a fixed assignment on $P$, the observation is $1$ exactly when that assignment is the specified $z$; otherwise it is $0$. Indeed, matching every coordinate forces the fixed assignment to equal $z$, and conversely that equality guarantees the match. The observation does not depend on the free coordinates, so averaging over them leaves the same indicator. Finally, a specified point in the space of assignments on $P$ has uniform probability $1/|\{ -1,1\}^{P}|$ (\texttt{uniformProbability_eq_singleton}). There are $2^{|P|}$ such assignments, giving probability $2^{-|P|}. The splitting identifies the fixed-assignment indicator with the original matching event using \texttt{juntaAssignmentSplitEquiv_symm_apply}.

**Key facts.** `FABL.juntaAssignmentSplitEquiv_symm_apply`, `FABL.uniformProbability_eq_singleton`.

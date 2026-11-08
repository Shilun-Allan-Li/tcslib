<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.solveF₂Pivots_satisfies -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfaction of triangular equations

**Claim.** Under the stated triangularity conditions, the assignment produced by recursively setting pivot variables satisfies every equation in the list.

**Proof.** Proceed by induction on the list of pivot pairs. The empty list has no equations to check. For a nonempty list, write its head as $(v,E)$ and its tail as the remaining pairs. The pivot coefficient of $E$ is $1$, and every equation in the tail has coefficient $0$ at $v$. Take any listed pair. If it is the head, setting $v$ by the pivot rule makes $E$ satisfied (\texttt{FABL.isSatisfied_setF₂PivotValue}). If it lies in the tail, changing the assignment at $v$ does not change that equation's value, because its coefficient there is zero; satisfaction after the update is therefore equivalent to satisfaction before it (\texttt{FABL.isSatisfied_setF₂PivotValue_iff_of_coefficient_eq_zero}). The induction hypothesis gives that prior satisfaction for every tail equation. Hence every equation in the list is satisfied.

**Key facts.** `FABL.isSatisfied_setF₂PivotValue`, `FABL.isSatisfied_setF₂PivotValue_iff_of_coefficient_eq_zero`.

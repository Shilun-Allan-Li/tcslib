<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.eliminateF₂Rows_work_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Elimination Work Bound

**Claim.** The work recorded by eliminating along $C$ is at most $|C|\,|R|\,(|\nu|+2)$.

**Proof.** Induct on the coordinate list, allowing the input rows to vary. With no coordinates, the recorded work is zero. At a processed coordinate with no pivot found, the current cost is the row count, followed by the recursive cost on the same rows. Since $|\nu|+2\geq1$, the current cost is at most $|R|(|\nu|+2)$; the induction bound controls the recursive term, and together these give the result for one more coordinate. If a pivot is found, the recursive input consists of the remaining rows after removing the pivot and clearing them. The remaining-row count is at most the original row count, since extraction removes exactly one row (`extractF₂Pivot_remaining_length`), and clearing does not change list length. Thus the current cost, $|R|+|R'|(|\nu|+1)$, is at most $|R|(|\nu|+2)$. By induction, the recursive work is at most the number of remaining coordinates times $|R|(|\nu|+2)$. Adding these bounds yields the claimed estimate.

**Key facts.** `FABL.extractF₂Pivot_remaining_length`.

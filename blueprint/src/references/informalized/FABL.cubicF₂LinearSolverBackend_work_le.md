<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixExponentSolver.lean :: FABL.cubicF₂LinearSolverBackend_work_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cubic Linear Solver Work Bound

**Claim.** For a finite list of linear equations over $\mathbb F_2$ in variables from a finite set $\nu$, the cubic solver's work is at most $|\nu|m(|\nu|+2)+|\nu|(|\nu|+1)$, where $m$ is the number of equations.

**Proof.** Run elimination over the coordinate list of $\nu$. Its elimination work is at most the number of coordinates times the number of rows times $|\nu|+2$ (\texttt{eliminateF₂Rows_work_le}); since the coordinate list enumerates $\nu$, this is $|\nu|m(|\nu|+2)$. The number of pivots is at most the number of coordinates (\texttt{eliminateF₂Rows_pivots_length_le}), hence at most $|\nu|$. The solver's total work adds to the elimination work the pivot count multiplied by $|\nu|+1$. Bounding these two terms separately and adding gives the claimed estimate.

**Key facts.** `FABL.eliminateF₂Rows_work_le`, `FABL.eliminateF₂Rows_pivots_length_le`.

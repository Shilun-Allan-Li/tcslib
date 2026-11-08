<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.solveF₂Rows_satisfies_of_exists -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Consistency of Gaussian elimination

**Claim.** If a finite system of linear equations over $\mathbb F_2$ has a satisfying assignment, then the assignment produced by the specified solver satisfies every equation.

**Proof.** Let the solver’s elimination produce pivot equations and residual rows. Since the original system has a satisfying assignment, the elimination equivalence theorem (`FABL.satisfiesRows_eliminateF₂Rows_iff`) implies that this witness satisfies every pivot equation and every residual row. The pivots are triangular (`FABL.isF₂Triangular_eliminateF₂Rows`), so the triangular pivot solver satisfies every pivot equation. For any residual row, every coordinate coefficient is zero: the residual-coefficient theorem (`FABL.eliminateF₂Rows_residual_coefficient_eq_zero_of_mem`) gives this for each coordinate in the solver’s coordinate list, which contains all coordinates. Thus the row evaluates to zero under the solver’s assignment. The witness satisfies that residual row, so its constant is also zero; hence the solver’s assignment satisfies it as well. The solver therefore satisfies both all pivots and all residual rows, and the elimination equivalence theorem gives satisfaction of every original row.

**Key facts.** `FABL.satisfiesRows_eliminateF₂Rows_iff`, `FABL.isF₂Triangular_eliminateF₂Rows`, `FABL.solveF₂Pivots_satisfies`, `FABL.eliminateF₂Rows_residual_coefficient_eq_zero_of_mem`.

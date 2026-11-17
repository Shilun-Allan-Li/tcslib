<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.satisfiesRows_eliminateF₂Rows_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfaction After Linear Elimination

**Claim.** An assignment satisfies every original equation exactly when it satisfies all recorded pivot equations and every equation in the residual list produced by elimination.

**Proof.** Proceed by induction on the list of variables used as potential pivots, generalizing over the input rows. With no variables left, elimination records no pivots and leaves the rows unchanged, so the claim follows directly. For a nonempty variable list, consider whether a pivot row is extracted. If none is found, the rows remain unchanged and the induction hypothesis for the remaining variables gives the result. If a pivot is found, the extraction identity splits satisfaction of the original rows into satisfaction of that pivot and of the remaining rows (`FABL.extractF₂Pivot_satisfiesRows_iff`). Assuming the pivot is satisfied, clearing its coefficient preserves satisfaction of the remaining rows in both directions (`FABL.satisfiesRows_clearF₂PivotRows_iff`). Apply the induction hypothesis to this cleared list. Its resulting pivots are exactly the later pivots, while the extracted pivot is added at the front; its residual equations are unchanged. Thus satisfaction of the original list is equivalent to satisfaction of the full pivot list and the final residual list.

**Key facts.** `FABL.extractF₂Pivot_satisfiesRows_iff`, `FABL.satisfiesRows_clearF₂PivotRows_iff`.

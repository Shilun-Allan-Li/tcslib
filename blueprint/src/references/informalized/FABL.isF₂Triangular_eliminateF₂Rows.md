<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.isF₂Triangular_eliminateF₂Rows -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Triangularity of Elimination Pivots

**Claim.** The specified row elimination procedure produces a pivot list in which each pivot has coefficient $1$ on its pivot variable, all later pivots have coefficient $0$ on that variable, and the same properties hold recursively throughout the list.

**Proof.** Proceed by induction on the ordered list of coordinates, allowing the input rows to vary. With no coordinates left, there are no pivots, so triangularity is vacuous. For a nonempty coordinate list, inspect whether the procedure finds a row with coefficient $1$ on the first coordinate. If it finds none, the procedure moves on to the remaining coordinates with the original rows, and the induction hypothesis gives triangularity. If it finds a pivot, that row has coefficient $1$ on the first coordinate (\(\texttt{FABL.extractF\u2082Pivot\_coefficient\_eq\_one}\)). The procedure clears this coordinate from each remaining row; adding the pivot where needed makes each cleared coefficient zero (\(\texttt{FABL.F\u2082LinearEquation.clearPivot\_coefficient\_eq\_zero}\)). The later pivots are obtained by eliminating the remaining coordinates from these cleared rows. Elimination preserves a zero column in every resulting pivot (\(\texttt{FABL.eliminateF\u2082Rows\_preserves\_zero\_column}\)), so every later pivot has coefficient zero on the first coordinate. The induction hypothesis makes the tail pivot list triangular, completing the result.

**Key facts.** `FABL.extractF₂Pivot_coefficient_eq_one`, `FABL.F₂LinearEquation.clearPivot_coefficient_eq_zero`, `FABL.eliminateF₂Rows_preserves_zero_column`.

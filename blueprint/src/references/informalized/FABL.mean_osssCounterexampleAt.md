<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.mean_osssCounterexampleAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Sign-Cube Polynomial

**Claim.** For every real \(t\), the mean of the specified polynomial \(P_t\) on the three-dimensional sign cube is \((t+1)/4\).

**Proof.** Write the uniform expectation on the three-dimensional sign cube as the average over its eight sign triples (\(\texttt{FABL.expect_signCube_three_eq}\)). Sum successively over each of the three signs; for a function of one sign, this sum is its value at \(+1\) plus its value at \(-1\) (\(\texttt{FABL.sum_sign_eq}\)). In the resulting average, every nonconstant monomial term cancels across the sign choices, leaving only the constant term \((t+1)/4\).

**Key facts.** `FABL.expect_signCube_three_eq`, `FABL.sum_sign_eq`.

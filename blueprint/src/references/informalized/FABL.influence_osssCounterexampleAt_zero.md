<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.influence_osssCounterexampleAt_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence at the First Coordinate

**Claim.** For every real $t$, the influence of the specified three-coordinate function at coordinate $0$ is $1/8$.

**Proof.** The discrete derivative at coordinate $0$ is $(-x_1+x_2)/4$, by the coordinate derivative formula (`FABL.discreteDerivative_osssCounterexampleAt_zero`). Its square, averaged over the three-coordinate sign cube, is the influence. Express the uniform expectation as the sum over all eight assignments divided by $8$ (`FABL.expect_signCube_three_eq`), and evaluate the finite sign sums by summing each sign over $1$ and $-1$ (`FABL.sum_sign_eq`). Since $x_1^2=x_2^2=1$ and the mixed term averages to zero, the result is $1/8$.

**Key facts.** `FABL.discreteDerivative_osssCounterexampleAt_zero`, `FABL.expect_signCube_three_eq`, `FABL.sum_sign_eq`.

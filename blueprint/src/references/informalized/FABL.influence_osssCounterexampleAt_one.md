<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.influence_osssCounterexampleAt_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence at Coordinate One

**Claim.** For every real $t$, the influence of the specified three-coordinate function at coordinate $1$ is $(t^2-t+1)/8$.

**Proof.** The discrete derivative at coordinate $1$ is $(t-x_0+(t-1)x_2)/4$, by the coordinate derivative formula (`FABL.discreteDerivative_osssCounterexampleAt_one`). The influence is the uniform average of the square of this expression. The three-coordinate expectation is the sum over all sign choices divided by $8$ (`FABL.expect_signCube_three_eq`); expanding that finite sum by summing each sign over $1$ and $-1$ (`FABL.sum_sign_eq`) leaves $(t^2-t+1)/8$ after using that each sign squares to $1$ and simplifying.

**Key facts.** `FABL.discreteDerivative_osssCounterexampleAt_one`, `FABL.expect_signCube_three_eq`, `FABL.sum_sign_eq`.

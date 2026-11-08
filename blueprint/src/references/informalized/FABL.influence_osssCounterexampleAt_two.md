<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.influence_osssCounterexampleAt_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence at the Third Coordinate

**Claim.** For every real $t$, the influence of the specified three-coordinate function at coordinate $2$ is $(t^2-t+1)/8$.

**Proof.** The discrete derivative at coordinate $2$ is $(t+x_0+(t-1)x_1)/4$, by the coordinate derivative formula (`FABL.discreteDerivative_osssCounterexampleAt_two`). The influence is the uniform average of its square. Write this expectation as a sum over the eight sign assignments divided by $8$ (`FABL.expect_signCube_three_eq`), then evaluate the sign sums using the fact that each sign takes the values $1$ and $-1$ (`FABL.sum_sign_eq`). Expanding and simplifying gives $(t^2-t+1)/8$.

**Key facts.** `FABL.discreteDerivative_osssCounterexampleAt_two`, `FABL.expect_signCube_three_eq`, `FABL.sum_sign_eq`.

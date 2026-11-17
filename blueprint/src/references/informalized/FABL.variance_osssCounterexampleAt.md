<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.variance_osssCounterexampleAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance of a Three-Cube Function

**Claim.** For every real parameter $t$, the displayed function on the three-dimensional sign cube has variance $(3t^2-2t+3)/16$.

**Proof.** The mean of this function is $(t+1)/4$ (`mean_osssCounterexampleAt`). Subtracting it from the function leaves its nonconstant terms together with the corresponding centered constant contribution. The expectation over the three-dimensional sign cube can be written as the average over all eight triples of signs (`expect_signCube_three_eq`); each sum over a sign coordinate reduces to its two values, $1$ and $-1$ (`sum_sign_eq`). Evaluating these finite sums and simplifying the resulting polynomial gives $(3t^2-2t+3)/16$.

**Key facts.** `FABL.mean_osssCounterexampleAt`, `FABL.expect_signCube_three_eq`, `FABL.sum_sign_eq`.

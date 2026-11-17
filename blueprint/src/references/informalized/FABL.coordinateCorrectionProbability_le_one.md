<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.coordinateCorrectionProbability_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correction Probability Bound

**Claim.** For every Boolean function, coordinate, and bit, the probability that the local correction agrees with the sign encoding of the bit is at most $1$.

**Proof.** For each input $y$, the indicator of the event is either $0$ or $1$, so it is at most the constant function $1$. Averaging this pointwise inequality over the finite uniform input space preserves the inequality. The average of the constant function $1$ is $1$, which gives the claimed bound.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.nandTree10_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the second NAND tree

**Claim.** The second decision tree computes the function on pairs of signs that returns $1$ exactly when both input coordinates are $-1$, and returns $-1$ otherwise.

**Proof.** Each coordinate is either $1$ or $-1$, so split into the four possible pairs of values. Evaluating the second tree along its prescribed branches gives output $1$ precisely for the pair $(-1,-1)$ and output $-1$ for the other three pairs. Its output therefore agrees with the NAND function on every input.

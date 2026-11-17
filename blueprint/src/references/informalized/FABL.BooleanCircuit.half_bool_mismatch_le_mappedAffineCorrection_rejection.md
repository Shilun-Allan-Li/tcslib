<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.half_bool_mismatch_le_mappedAffineCorrection_rejection -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mismatch Forces Correction Rejection

**Claim.** If the affine-coordinate correction returns the sign encoding of $b_0$ with probability at least $1/2$, then the stated mismatch penalty for $b$ is at most one minus the probability that the correction returns the sign encoding of $b$.

**Proof.** If $b=b_0$, the left side is zero, and the result follows because the correction probability is at most one (`FABL.affineCoordinateCorrectionProbability_le_one`). Otherwise the left side is $1/2$. The correction output is always one of the two signs, so the probabilities of outputs $1$ and $-1$ sum to one (`FABL.uniformProbability_sign_eq_one_add_neg_one_eq_one`). The encodings of the two distinct Boolean values are these two opposite signs. Thus the hypothesis says that the probability of the sign encoding $b_0$ is at least $1/2$, so the probability of the other sign is at most $1/2$. Equivalently, one minus the probability of outputting the sign encoding of $b$ is at least $1/2$, as required.

**Key facts.** `FABL.affineCoordinateCorrectionProbability_le_one`, `FABL.uniformProbability_sign_eq_one_add_neg_one_eq_one`.

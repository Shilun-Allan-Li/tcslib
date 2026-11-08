<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.half_relativeHammingDist_le_circuitQuadraticInputConsistency_rejection -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Distance Bounds Tester Rejection

**Claim.** Under the coordinatewise correction hypothesis, half the relative Hamming distance between $w$ and $w_0$ is at most one minus the acceptance probability of the input-consistency tester on the concatenation of $w$ and the proof.

**Proof.** The tester's acceptance probability is the average, over input coordinates, of the affine-correction probability for the corresponding bit of $w$ (`FABL.BooleanCircuit.circuitQuadraticInputConsistencyFunctionTester_acceptanceProbability`). The relative Hamming distance is the uniform probability that the two words disagree (`FABL.uniformProbability_ne_eq_relativeHammingDist`), so half that distance is the average of the coordinatewise mismatch indicators, each multiplied by $1/2$. At each coordinate, apply the mismatch-versus-rejection bound using the hypothesis that correction returns the sign encoding of $w_0$ with probability at least $1/2$ (`FABL.BooleanCircuit.half_bool_mismatch_le_mappedAffineCorrection_rejection`). Averaging these inequalities bounds half the relative distance by the average of one minus the correction probability for $w$. Since the average of $1$ minus these probabilities is one minus their average, the tester's acceptance-probability identity gives the claimed bound.

**Key facts.** `FABL.BooleanCircuit.circuitQuadraticInputConsistencyFunctionTester_acceptanceProbability`, `FABL.uniformProbability_ne_eq_relativeHammingDist`, `FABL.BooleanCircuit.half_bool_mismatch_le_mappedAffineCorrection_rejection`.

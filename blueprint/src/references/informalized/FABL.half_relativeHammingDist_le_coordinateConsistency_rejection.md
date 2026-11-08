<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.half_relativeHammingDist_le_coordinateConsistency_rejection -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distance and Rejection Bound

**Claim.** Under the stated correctness hypothesis for the coordinate correction probabilities, half the relative Hamming distance between $w$ and $w_0$ is at most the coordinate consistency tester's rejection probability.

**Proof.** The tester's acceptance probability is the average, over coordinates $j$, of the probability that the correction outputs $w_j$ (`coordinateConsistencyFunctionTester_acceptanceProbability`). The hypothesis says that the correction outputs $w_0(j)$ with probability at least $1/2$. Consequently, whenever $w(j)\ne w_0(j)$, the probability it outputs $w(j)$ is at most $1/2$; thus half the mismatch indicator is bounded by one minus the probability of outputting $w(j)$ (`half_mismatch_le_coordinateCorrection_rejection`). Average this inequality over all coordinates. The average mismatch indicator is the relative Hamming distance (`uniformProbability_ne_eq_relativeHammingDist`), and the average of one minus the coordinate success probabilities is one minus their average. Using the tester's acceptance formula identifies that last quantity with its rejection probability, proving the bound.

**Key facts.** `FABL.coordinateConsistencyFunctionTester_acceptanceProbability`, `FABL.half_mismatch_le_coordinateCorrection_rejection`, `FABL.uniformProbability_ne_eq_relativeHammingDist`.

**Caveat.** The payload's informal statement describes a different Markov-inequality conclusion; this proof follows the supplied formal statement and proof source.

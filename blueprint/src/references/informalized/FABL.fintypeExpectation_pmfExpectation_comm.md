<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.fintypeExpectation_pmfExpectation_comm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Interchanging finite expectations

**Claim.** A uniform average over a finite index set of expectations under a probability mass function equals the expectation of the uniform average.

**Proof.** Expand each uniform expectation as a finite sum divided by the cardinality of the index set, and expand the probability-mass expectation as the sum over outcomes weighted by their probabilities. Interchange the two finite sums; finite sums commute. For each outcome, factor its probability weight out of the uniform sum. The resulting expression is the probability-mass expectation of the uniform average, as claimed.

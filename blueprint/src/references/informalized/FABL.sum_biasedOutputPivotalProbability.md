<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.sum_biasedOutputPivotalProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum of Biased Output Pivotal Probabilities

**Claim.** The sum of the biased output pivotal probabilities over coordinates equals the expectation of the number of output-pivotal coordinates.

**Proof.** By definition, each coordinate's biased output pivotal probability is the expectation of the indicator that this coordinate is output-pivotal. Linearity of finite PMF expectation (`FABL.pmfExpectation_sum`) moves the coordinate sum inside the expectation. At each input, the sum of these indicators is the output-pivotal count, expressed as a real number (`FABL.outputPivotalCount_cast`). Substituting this pointwise identity gives the claimed expectation.

**Key facts.** `FABL.pmfExpectation_sum`, `FABL.outputPivotalCount_cast`.

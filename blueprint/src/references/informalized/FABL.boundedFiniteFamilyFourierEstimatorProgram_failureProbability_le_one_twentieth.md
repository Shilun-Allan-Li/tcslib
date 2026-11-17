<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.boundedFiniteFamilyFourierEstimatorProgram_failureProbability_le_one_twentieth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Estimator Failure Probability

**Claim.** If the target spectrum has at most $\varepsilon/2$ Fourier weight outside the nonempty family $\mathcal F$, with $|\mathcal F|\le M$, then the bounded-family estimator has failure probability at most $1/20$.

**Proof.** Let the failure event consist of sample matrices for which the estimator's hypothesis has relative Hamming distance greater than $\varepsilon$ from the target. If no member $S$ of the family has a bad coefficient estimate, the deterministic accuracy result for the bounded-family output, together with the assumed spectral concentration, shows that this distance is at most $\varepsilon$. Thus failure implies that at least one family member has a bad estimate, so the failure event is contained in the union of those bad-coefficient events.

The estimator's outcome law is the image of the uniform sample-matrix law under the map producing the output and its cost. Consequently, the probability of estimator failure is the sample-matrix probability of the failure event. By monotonicity of measure and the finite-family bad-coefficient bound, this is at most $|\mathcal F|$ times the confidence parameter. That parameter is $1/(20M)$. Since $|\mathcal F|\le M$, the product is at most $1/20$, as required.

**Key facts.** `FABL.LearningProgram.randomExampleMatrixOutputLaw_toOuterMeasure_apply`, `FABL.relativeHammingDist_boundedFiniteFamilyOutput_le_of_no_bad`, `FABL.measure_finiteFamily_someCoefficientBadSetWithParameters_le`.

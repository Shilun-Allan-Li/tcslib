<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.measure_lowDegreeF₂MissSet_eq_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of missing a polynomial

**Claim.** For a uniformly random $m$-tuple of Boolean-cube points, the probability that a given low-degree polynomial vanishes at every sampled point is the $m$th power of the fraction of points where it vanishes.

**Proof.** The event that the polynomial vanishes at every coordinate of the sample tuple is the product event whose coordinate event is that it vanishes at one point. The uniform measure on tuples is the product of the uniform measures on the individual cube points (`uniformSample_toMeasure_eq_pi`). The measure of this product event is therefore the product of the $m$ identical coordinate probabilities. Each coordinate probability equals the uniform fraction of cube points where the polynomial vanishes (`measure_uniformPMF_event_eq_uniformProbability`). Multiplying these $m$ equal factors gives the claimed $m$th power, including the empty product when $m=0$.

**Key facts.** `FABL.uniformSample_toMeasure_eq_pi`, `FABL.measure_uniformPMF_event_eq_uniformProbability`.

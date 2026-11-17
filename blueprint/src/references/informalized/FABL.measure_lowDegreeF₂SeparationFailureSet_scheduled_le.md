<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.measure_lowDegreeF₂SeparationFailureSet_scheduled_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scheduled separation guarantee

**Claim.** For the specified sample count determined by $n$, $\ell$, and $\delta$, the probability that the samples fail to distinguish degree-at-most-$\ell$ coefficient functions is at most $\delta$.

**Proof.** The prescribed sample count satisfies the budget inequality for the general separation estimate (`lowDegreeF₂LearningSampleCount_budget_le`). Applying the failure-probability bound under that budget (`measure_lowDegreeF₂SeparationFailureSet_le_of_budget`) gives the claimed upper bound $\delta$.

**Key facts.** `FABL.lowDegreeF₂LearningSampleCount_budget_le`, `FABL.measure_lowDegreeF₂SeparationFailureSet_le_of_budget`.

**Caveat.** The formal theorem establishes the scheduled separation probability bound only; it does not establish the additional sample-complexity or runtime claims in the supplied informal statement.

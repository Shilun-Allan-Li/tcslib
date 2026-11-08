<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.scheduledLowDegreeF₂PolynomialLearnerProgram_sampleCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scheduled Sample Count Identity

**Claim.** The scheduled low degree learner's sample count equals the number of monomials plus the failure-bit count, multiplied by $2^\ell$.

**Proof.** By definition, the scheduled sample count is $2^\ell$ times the sum of the low degree monomial count and the failure-bit count. The latter is defined as $\operatorname{Nat.clog}(2,\lceil 2/\delta\rceil)$, so the displayed expression is exactly the same quantity.

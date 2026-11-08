<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.rationalRestrictedFourierWeightEstimateFromAnswers_cast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted estimate cast

**Claim.** The rational estimate obtained from the answers, regarded as real, equals the corresponding real-valued estimate.

**Proof.** Expand the outer expectation as the average over its finite sample set. Each rational inner average has terms given by the rational answer value times the rational indexed monomial; casting each term gives the real sign value times the real monomial, by preservation of products and the indexed-monomial cast identity. Casting also preserves the finite sums, division by the sample counts, and squaring. Thus each outer summand becomes the corresponding squared real inner average, and the outer average is exactly the stated real estimate.

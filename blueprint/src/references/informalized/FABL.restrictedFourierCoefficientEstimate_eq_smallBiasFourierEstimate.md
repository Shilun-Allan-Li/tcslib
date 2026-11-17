<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.restrictedFourierCoefficientEstimate_eq_smallBiasFourierEstimate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted Fourier estimate identity

**Claim.** The restricted Fourier coefficient estimate equals the small-bias Fourier estimate of the function on the free coordinates, using the reindexed frequency set.

**Proof.** Expand both estimates as sums divided by the same sample count. For each sample, the values of the restricted target agree by definition. The remaining factors agree because the monomial on the reindexed frequency set equals the indexed monomial on the corresponding free-sign assignment (`monomial_freeFrequencyReindex`). Thus the summands agree term by term, and so do the normalized sums.

**Key facts.** `FABL.monomial_freeFrequencyReindex`.

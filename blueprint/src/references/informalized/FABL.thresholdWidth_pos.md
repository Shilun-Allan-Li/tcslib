<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.thresholdWidth_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Threshold Width

**Claim.** Under the stated assumptions, the threshold width is positive.

**Proof.** The lower threshold parameter lies strictly below the critical probability, and the critical probability lies strictly below the upper threshold parameter (`thresholdLower_lt_critical_lt_thresholdUpper`). Hence the upper threshold parameter is strictly greater than the lower one. Their difference, which is the threshold width by definition, is therefore positive.

**Key facts.** `FABL.thresholdLower_lt_critical_lt_thresholdUpper`.

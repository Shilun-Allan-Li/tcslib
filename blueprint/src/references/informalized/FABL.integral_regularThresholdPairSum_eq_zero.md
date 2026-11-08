<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.integral_regularThresholdPairSum_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of the correlated pair sum

**Claim.** For the correlated sign-pair distribution described, the expected sum over coordinates of the vectors $(a_i x_i,a_i y_i)$ is the zero vector.

**Proof.** Write the sum as a finite sum of its coordinate summands. Each summand is integrable, as follows from its finite third moment (`regularThresholdPairSummand_memLp`). Linearity of integration for finite sums then reduces the claim to the mean of each individual summand. Each such mean is zero by the correlated-pair summand mean theorem (`integral_regularThresholdPairSummand_eq_zero`), so their finite sum is zero.

**Key facts.** `FABL.regularThresholdPairSummand_memLp`, `FABL.integral_regularThresholdPairSummand_eq_zero`.

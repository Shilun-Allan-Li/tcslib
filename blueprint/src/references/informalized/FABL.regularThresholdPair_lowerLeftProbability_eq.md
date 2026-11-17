<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.regularThresholdPair_lowerLeftProbability_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower-Left Probability as an Acceptance Expectation

**Claim.** The probability that the pair sum lies in the lower-left quadrant equals the expectation of the indicator that both threshold values are $-1$.

**Proof.** Let $A$ be the event that the pair sum lies in the lower-left quadrant. The sum is measurable on the finite space, and the quadrant is measurable (`FABL.measurableSet_signQuadrant`), so $A$ is measurable. The measure of the image event under the sum is therefore the measure of its preimage, by the measure-of-a-preimage formula for pushforward measures. Express this event's measure as the integral of its indicator, then use the identity between the finite PMF expectation and integration (`FABL.pmfExpectation_eq_integral`). Finally, the lower-left quadrant characterization (`FABL.regularThresholdPairSum_mem_lowerLeft_iff`) identifies membership in $A$ with both function values being $-1$. Their indicators agree pointwise, so their expectations agree.

**Key facts.** `FABL.measurableSet_signQuadrant`, `FABL.pmfExpectation_eq_integral`, `FABL.regularThresholdPairSum_mem_lowerLeft_iff`.

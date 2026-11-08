<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.outputPivotalCount_cast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator sum for output-pivotal coordinates

**Claim.** The real-valued count of coordinates at which $f$ is pivotal at $x$ and $f(x)=b$ equals the sum of the indicators of those conditions over all coordinates.

**Proof.** The count is the cardinality of the finite set of coordinates satisfying the two conditions. A finite set's cardinality is the sum, over all coordinates, of the indicator of membership. Casting that cardinality to the reals turns the natural-number sum into a real sum, and each membership indicator is exactly $1$ when the conditions hold and $0$ otherwise.

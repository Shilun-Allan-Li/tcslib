<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/EdgeIsoperimetric.lean :: FABL.abs_positiveProbability_sub_le_uniformProbability_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Probability Difference Bound

**Claim.** For Boolean functions $f,g$ on the uniform cube, the absolute difference between the probabilities that they equal $1$ is at most the probability that they disagree.

**Proof.** Write each event indicator as a real-valued function on the cube. By linearity of expectation, the difference of the two probabilities is the expectation of the difference of these indicators. The absolute value of an expectation is at most the expectation of the absolute value. Pointwise, the absolute difference of the indicators is $0$ when $f(x)=g(x)$ and at most $1$ otherwise: since both outputs are signs, if they differ, one equals $1$ and the other does not. Thus this absolute difference is bounded by the indicator of disagreement. Averaging gives the claimed bound.

<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.quadraticPairRankOne_rejectionProbability_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection as a Disagreement Average

**Claim.** One minus the rank-one acceptance probability is the uniform average of the indicator that ℓ(x)ℓ(y) differs from q(Z)+q(Z+xyᵀ).

**Proof.** Write the acceptance probability as the iterated uniform average of the indicator of the equality ℓ(x)ℓ(y)=q(Z)+q(Z+xyᵀ). The constant 1 is itself the iterated average of the constant-one function. Subtracting the acceptance average from this constant, and using linearity of expectation at each of the three averaging stages, gives the average of one minus the equality indicator. For each fixed triple, this difference is 1 exactly when the two sides differ and 0 when they agree. It is therefore the indicator of disagreement, as claimed.

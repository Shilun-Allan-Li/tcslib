<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.productCovariance_eq_restrictionAverage_add_laplacian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction covariance decomposition

**Claim.** The product covariance equals the average of covariances of independent coordinate restrictions plus the product inner product of the coordinate Laplacians.

**Proof.** First, the average of restricted covariances is the covariance of the coordinate projections (`restrictionCovarianceAverage_eq_projection_covariance`). Substitute this identity into the desired formula. The covariance decomposition by coordinate states that the covariance of $f$ and $g$ is the covariance of their coordinate projections plus the inner product of their coordinate Laplacians (`productCovariance_eq_projection_covariance_add_laplacian`). Combining the two identities gives the result.

**Key facts.** `FABL.restrictionCovarianceAverage_eq_projection_covariance`, `FABL.productCovariance_eq_projection_covariance_add_laplacian`.
